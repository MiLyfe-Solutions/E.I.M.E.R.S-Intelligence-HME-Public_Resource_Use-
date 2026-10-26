import V185TrunkScan19Chunk035

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_361213 : List Nat := [1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_361213 : Nat := 118140960795 + 361213 * 2 ^ 59
def prefixEnd_361213 : Nat := 4983230072969 + 3 ^ 40 * 361213 * 2
def baseEnd_361213 : Nat := 109911637127466954771151

theorem tailTrace_361213 : CollatzResearch.WordTrace tailWord_361213 prefixEnd_361213 109911637127466954771151 := by
  unfold tailWord_361213
  simp only [CollatzResearch.WordTrace]
  refine ⟨13174520440394466114096293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8783013626929644076064195 13174520440394466114096293)
  ·
    refine ⟨2470222582573962396393055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13174520440394466114096293 2470222582573962396393055)
    ·
      refine ⟨3705333873860943594589583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2470222582573962396393055 3705333873860943594589583)
      ·
        refine ⟨5558000810791415391884375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3705333873860943594589583 5558000810791415391884375)
        ·
          refine ⟨8337001216187123087826563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5558000810791415391884375 8337001216187123087826563)
          ·
            refine ⟨12505501824280684631739845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8337001216187123087826563 12505501824280684631739845)
            ·
              refine ⟨2344781592052628368451221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12505501824280684631739845 2344781592052628368451221)
              ·
                refine ⟨109911637127466954771151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2344781592052628368451221 109911637127466954771151)
                ·
                  rfl

theorem cell19_361213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_361213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361213 prefixEnd_361213 := by exact prefixLift 361213
  have htrace : WordTrace (prefixWord ++ tailWord_361213) baseStart_361213 baseEnd_361213 := by
    simpa [prefixWord, tailWord_361213, baseEnd_361213] using wordTrace_append hprefix tailTrace_361213
  have hstable : (prefixWord ++ tailWord_361213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361213).length < 2 ^ (prefixWord ++ tailWord_361213).sum := by decide
  have hdescent : baseEnd_361213 < baseStart_361213 := by decide
  rcases family_descends (prefixWord ++ tailWord_361213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361245 : List Nat := [1, 4, 2, 4, 2, 1, 5]
def baseStart_361245 : Nat := 118140960795 + 361245 * 2 ^ 59
def prefixEnd_361245 : Nat := 4983230072969 + 3 ^ 40 * 361245 * 2
def baseEnd_361245 : Nat := 36640458080700120686651

theorem tailTrace_361245 : CollatzResearch.WordTrace tailWord_361245 prefixEnd_361245 36640458080700120686651 := by
  unfold tailWord_361245
  simp only [CollatzResearch.WordTrace]
  refine ⟨13175687576278535579261189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8783791717519023719507459 13175687576278535579261189)
  ·
    refine ⟨2470441420552225421111473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13175687576278535579261189 2470441420552225421111473)
    ·
      refine ⟨1852831065414169065833605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2470441420552225421111473 1852831065414169065833605)
      ·
        refine ⟨347405824765156699843801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1852831065414169065833605 347405824765156699843801)
        ·
          refine ⟨260554368573867524882851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347405824765156699843801 260554368573867524882851)
          ·
            refine ⟨390831552860801287324277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260554368573867524882851 390831552860801287324277)
            ·
              refine ⟨36640458080700120686651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 390831552860801287324277 36640458080700120686651)
              ·
                rfl

theorem cell19_361245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 5].length) (baseStart_361245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361245 prefixEnd_361245 := by exact prefixLift 361245
  have htrace : WordTrace (prefixWord ++ tailWord_361245) baseStart_361245 baseEnd_361245 := by
    simpa [prefixWord, tailWord_361245, baseEnd_361245] using wordTrace_append hprefix tailTrace_361245
  have hstable : (prefixWord ++ tailWord_361245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361245).length < 2 ^ (prefixWord ++ tailWord_361245).sum := by decide
  have hdescent : baseEnd_361245 < baseStart_361245 := by decide
  rcases family_descends (prefixWord ++ tailWord_361245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361289 : List Nat := [1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_361289 : Nat := 118140960795 + 361289 * 2 ^ 59
def prefixEnd_361289 : Nat := 4983230072969 + 3 ^ 40 * 361289 * 2
def baseEnd_361289 : Nat := 109934762774721297082055

theorem tailTrace_361289 : CollatzResearch.WordTrace tailWord_361289 prefixEnd_361289 109934762774721297082055 := by
  unfold tailWord_361289
  simp only [CollatzResearch.WordTrace]
  refine ⟨13177292388119131093862921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8784861592079420729241947 13177292388119131093862921)
  ·
    refine ⟨9882969291089348320397191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13177292388119131093862921 9882969291089348320397191)
    ·
      refine ⟨14824453936634022480595787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9882969291089348320397191 14824453936634022480595787)
      ·
        refine ⟨22236680904951033720893681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14824453936634022480595787 22236680904951033720893681)
        ·
          refine ⟨16677510678713275290670261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22236680904951033720893681 16677510678713275290670261)
          ·
            refine ⟨1563516626129369558500337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16677510678713275290670261 1563516626129369558500337)
            ·
              refine ⟨1172637469597027168875253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563516626129369558500337 1172637469597027168875253)
              ·
                refine ⟨109934762774721297082055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1172637469597027168875253 109934762774721297082055)
                ·
                  rfl

theorem cell19_361289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_361289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361289 prefixEnd_361289 := by exact prefixLift 361289
  have htrace : WordTrace (prefixWord ++ tailWord_361289) baseStart_361289 baseEnd_361289 := by
    simpa [prefixWord, tailWord_361289, baseEnd_361289] using wordTrace_append hprefix tailTrace_361289
  have hstable : (prefixWord ++ tailWord_361289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361289).length < 2 ^ (prefixWord ++ tailWord_361289).sum := by decide
  have hdescent : baseEnd_361289 < baseStart_361289 := by decide
  rcases family_descends (prefixWord ++ tailWord_361289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361365 : List Nat := [1, 3, 2, 1, 1, 5, 6]
def baseStart_361365 : Nat := 118140960795 + 361365 * 2 ^ 59
def prefixEnd_361365 : Nat := 4983230072969 + 3 ^ 40 * 361365 * 2
def baseEnd_361365 : Nat := 36652629473991879797653

theorem tailTrace_361365 : CollatzResearch.WordTrace tailWord_361365 prefixEnd_361365 36652629473991879797653 := by
  unfold tailWord_361365
  simp only [CollatzResearch.WordTrace]
  refine ⟨13180064335843796073629549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8786709557229197382419699 13180064335843796073629549)
  ·
    refine ⟨4942524125941423527611081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13180064335843796073629549 4942524125941423527611081)
    ·
      refine ⟨3706893094456067645708311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4942524125941423527611081 3706893094456067645708311)
      ·
        refine ⟨5560339641684101468562467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706893094456067645708311 5560339641684101468562467)
        ·
          refine ⟨8340509462526152202843701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560339641684101468562467 8340509462526152202843701)
          ·
            refine ⟨781922762111826769016597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8340509462526152202843701 781922762111826769016597)
            ·
              refine ⟨36652629473991879797653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 781922762111826769016597 36652629473991879797653)
              ·
                rfl

theorem cell19_361365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_361365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361365 prefixEnd_361365 := by exact prefixLift 361365
  have htrace : WordTrace (prefixWord ++ tailWord_361365) baseStart_361365 baseEnd_361365 := by
    simpa [prefixWord, tailWord_361365, baseEnd_361365] using wordTrace_append hprefix tailTrace_361365
  have hstable : (prefixWord ++ tailWord_361365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361365).length < 2 ^ (prefixWord ++ tailWord_361365).sum := by decide
  have hdescent : baseEnd_361365 < baseStart_361365 := by decide
  rcases family_descends (prefixWord ++ tailWord_361365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361401 : List Nat := [1, 2, 1, 4, 2, 2, 4, 3]
def baseStart_361401 : Nat := 118140960795 + 361401 * 2 ^ 59
def prefixEnd_361401 : Nat := 4983230072969 + 3 ^ 40 * 361401 * 2
def baseEnd_361401 : Nat := 109968842675938222592861

theorem tailTrace_361401 : CollatzResearch.WordTrace tailWord_361401 prefixEnd_361401 109968842675938222592861 := by
  unfold tailWord_361401
  simp only [CollatzResearch.WordTrace]
  refine ⟨13181377363713374221940057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8787584909142249481293371 13181377363713374221940057)
  ·
    refine ⟨9886033022785030666455043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13181377363713374221940057 9886033022785030666455043)
    ·
      refine ⟨14829049534177545999682565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9886033022785030666455043 14829049534177545999682565)
      ·
        refine ⟨2780446787658289874940481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14829049534177545999682565 2780446787658289874940481)
        ·
          refine ⟨2085335090743717406205361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2780446787658289874940481 2085335090743717406205361)
          ·
            refine ⟨1564001318057788054654021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2085335090743717406205361 1564001318057788054654021)
            ·
              refine ⟨293250247135835260247629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1564001318057788054654021 293250247135835260247629)
              ·
                refine ⟨109968842675938222592861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293250247135835260247629 109968842675938222592861)
                ·
                  rfl

theorem cell19_361401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_361401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361401 prefixEnd_361401 := by exact prefixLift 361401
  have htrace : WordTrace (prefixWord ++ tailWord_361401) baseStart_361401 baseEnd_361401 := by
    simpa [prefixWord, tailWord_361401, baseEnd_361401] using wordTrace_append hprefix tailTrace_361401
  have hstable : (prefixWord ++ tailWord_361401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361401).length < 2 ^ (prefixWord ++ tailWord_361401).sum := by decide
  have hdescent : baseEnd_361401 < baseStart_361401 := by decide
  rcases family_descends (prefixWord ++ tailWord_361401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361422 : List Nat := [4, 1, 1, 1, 2, 3, 7]
def baseStart_361422 : Nat := 118140960795 + 361422 * 2 ^ 59
def prefixEnd_361422 : Nat := 4983230072969 + 3 ^ 40 * 361422 * 2
def baseEnd_361422 : Nat := 36658410885805465375379

theorem tailTrace_361422 : CollatzResearch.WordTrace tailWord_361422 prefixEnd_361422 36658410885805465375379 := by
  unfold tailWord_361422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647767912079661851056815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8788095531091529872303013 1647767912079661851056815)
  ·
    refine ⟨2471651868119492776585223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1647767912079661851056815 2471651868119492776585223)
    ·
      refine ⟨3707477802179239164877835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2471651868119492776585223 3707477802179239164877835)
      ·
        refine ⟨5561216703268858747316753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707477802179239164877835 5561216703268858747316753)
        ·
          refine ⟨4170912527451644060487565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5561216703268858747316753 4170912527451644060487565)
          ·
            refine ⟨1564092197794366522682837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4170912527451644060487565 1564092197794366522682837)
            ·
              refine ⟨36658410885805465375379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1564092197794366522682837 36658410885805465375379)
              ·
                rfl

theorem cell19_361422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_361422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361422 prefixEnd_361422 := by exact prefixLift 361422
  have htrace : WordTrace (prefixWord ++ tailWord_361422) baseStart_361422 baseEnd_361422 := by
    simpa [prefixWord, tailWord_361422, baseEnd_361422] using wordTrace_append hprefix tailTrace_361422
  have hstable : (prefixWord ++ tailWord_361422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361422).length < 2 ^ (prefixWord ++ tailWord_361422).sum := by decide
  have hdescent : baseEnd_361422 < baseStart_361422 := by decide
  rcases family_descends (prefixWord ++ tailWord_361422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361439 : List Nat := [1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_361439 : Nat := 118140960795 + 361439 * 2 ^ 59
def prefixEnd_361439 : Nat := 4983230072969 + 3 ^ 40 * 361439 * 2
def baseEnd_361439 : Nat := 109980405499565393748313

theorem tailTrace_361439 : CollatzResearch.WordTrace tailWord_361439 prefixEnd_361439 109980405499565393748313 := by
  unfold tailWord_361439
  simp only [CollatzResearch.WordTrace]
  refine ⟨13182763337575706711823371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8788508891717137807882247 13182763337575706711823371)
  ·
    refine ⟨19774145006363560067735057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13182763337575706711823371 19774145006363560067735057)
    ·
      refine ⟨14830608754772670050801293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19774145006363560067735057 14830608754772670050801293)
      ·
        refine ⟨5561478283039751269050485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14830608754772670050801293 5561478283039751269050485)
        ·
          refine ⟨521388589034976681473483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5561478283039751269050485 521388589034976681473483)
          ·
            refine ⟨782082883552465022210225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521388589034976681473483 782082883552465022210225)
            ·
              refine ⟨586562162664348766657669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782082883552465022210225 586562162664348766657669)
              ·
                refine ⟨109980405499565393748313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586562162664348766657669 109980405499565393748313)
                ·
                  rfl

theorem cell19_361439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_361439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361439 prefixEnd_361439 := by exact prefixLift 361439
  have htrace : WordTrace (prefixWord ++ tailWord_361439) baseStart_361439 baseEnd_361439 := by
    simpa [prefixWord, tailWord_361439, baseEnd_361439] using wordTrace_append hprefix tailTrace_361439
  have hstable : (prefixWord ++ tailWord_361439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361439).length < 2 ^ (prefixWord ++ tailWord_361439).sum := by decide
  have hdescent : baseEnd_361439 < baseStart_361439 := by decide
  rcases family_descends (prefixWord ++ tailWord_361439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361490 : List Nat := [3, 2, 5, 1, 1, 2, 1, 4]
def baseStart_361490 : Nat := 118140960795 + 361490 * 2 ^ 59
def prefixEnd_361490 : Nat := 4983230072969 + 3 ^ 40 * 361490 * 2
def baseEnd_361490 : Nat := 109995924026012386614841

theorem tailTrace_361490 : CollatzResearch.WordTrace tailWord_361490 prefixEnd_361490 109995924026012386614841 := by
  unfold tailWord_361490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296155865097735605482481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8789748973593961614619949 3296155865097735605482481)
  ·
    refine ⟨2472116898823301704111861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3296155865097735605482481 2472116898823301704111861)
    ·
      refine ⟨231760959264684534760487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2472116898823301704111861 231760959264684534760487)
      ·
        refine ⟨347641438897026802140731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231760959264684534760487 347641438897026802140731)
        ·
          refine ⟨521462158345540203211097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347641438897026802140731 521462158345540203211097)
          ·
            refine ⟨391096618759155152408323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521462158345540203211097 391096618759155152408323)
            ·
              refine ⟨586644928138732728612485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391096618759155152408323 586644928138732728612485)
              ·
                refine ⟨109995924026012386614841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586644928138732728612485 109995924026012386614841)
                ·
                  rfl

theorem cell19_361490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_361490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361490 prefixEnd_361490 := by exact prefixLift 361490
  have htrace : WordTrace (prefixWord ++ tailWord_361490) baseStart_361490 baseEnd_361490 := by
    simpa [prefixWord, tailWord_361490, baseEnd_361490] using wordTrace_append hprefix tailTrace_361490
  have hstable : (prefixWord ++ tailWord_361490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361490).length < 2 ^ (prefixWord ++ tailWord_361490).sum := by decide
  have hdescent : baseEnd_361490 < baseStart_361490 := by decide
  rcases family_descends (prefixWord ++ tailWord_361490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361496 : List Nat := [2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_361496 : Nat := 118140960795 + 361496 * 2 ^ 59
def prefixEnd_361496 : Nat := 4983230072969 + 3 ^ 40 * 361496 * 2
def baseEnd_361496 : Nat := 109997749735006150481491

theorem tailTrace_361496 : CollatzResearch.WordTrace tailWord_361496 prefixEnd_361496 109997749735006150481491 := by
  unfold tailWord_361496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592421149184602723324171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8789894865579470297765561 6592421149184602723324171)
  ·
    refine ⟨9888631723776904084986257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6592421149184602723324171 9888631723776904084986257)
    ·
      refine ⟨7416473792832678063739693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9888631723776904084986257 7416473792832678063739693)
      ·
        refine ⟨2781177672312254273902385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7416473792832678063739693 2781177672312254273902385)
        ·
          refine ⟨2085883254234190705426789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2781177672312254273902385 2085883254234190705426789)
          ·
            refine ⟨391103110168910757267523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2085883254234190705426789 391103110168910757267523)
            ·
              refine ⟨586654665253366135901285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391103110168910757267523 586654665253366135901285)
              ·
                refine ⟨109997749735006150481491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586654665253366135901285 109997749735006150481491)
                ·
                  rfl

theorem cell19_361496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_361496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361496 prefixEnd_361496 := by exact prefixLift 361496
  have htrace : WordTrace (prefixWord ++ tailWord_361496) baseStart_361496 baseEnd_361496 := by
    simpa [prefixWord, tailWord_361496, baseEnd_361496] using wordTrace_append hprefix tailTrace_361496
  have hstable : (prefixWord ++ tailWord_361496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361496).length < 2 ^ (prefixWord ++ tailWord_361496).sum := by decide
  have hdescent : baseEnd_361496 < baseStart_361496 := by decide
  rcases family_descends (prefixWord ++ tailWord_361496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361534 : List Nat := [4, 2, 1, 3, 1, 2, 6]
def baseStart_361534 : Nat := 118140960795 + 361534 * 2 ^ 59
def prefixEnd_361534 : Nat := 4983230072969 + 3 ^ 40 * 361534 * 2
def baseEnd_361534 : Nat := 36669770852877773878981

theorem tailTrace_361534 : CollatzResearch.WordTrace tailWord_361534 prefixEnd_361534 36669770852877773878981 := by
  unfold tailWord_361534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648278534028942242066457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8790818848154358624354437 1648278534028942242066457)
  ·
    refine ⟨1236208900521706681549843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1648278534028942242066457 1236208900521706681549843)
    ·
      refine ⟨1854313350782560022324765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236208900521706681549843 1854313350782560022324765)
      ·
        refine ⟨695367506543460008371787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1854313350782560022324765 695367506543460008371787)
        ·
          refine ⟨1043051259815190012557681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695367506543460008371787 1043051259815190012557681)
          ·
            refine ⟨782288444861392509418261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1043051259815190012557681 782288444861392509418261)
            ·
              refine ⟨36669770852877773878981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 782288444861392509418261 36669770852877773878981)
              ·
                rfl

theorem cell19_361534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_361534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361534 prefixEnd_361534 := by exact prefixLift 361534
  have htrace : WordTrace (prefixWord ++ tailWord_361534) baseStart_361534 baseEnd_361534 := by
    simpa [prefixWord, tailWord_361534, baseEnd_361534] using wordTrace_append hprefix tailTrace_361534
  have hstable : (prefixWord ++ tailWord_361534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361534).length < 2 ^ (prefixWord ++ tailWord_361534).sum := by decide
  have hdescent : baseEnd_361534 < baseStart_361534 := by decide
  rcases family_descends (prefixWord ++ tailWord_361534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361566 : List Nat := [4, 4, 1, 1, 1, 3, 2, 3]
def baseStart_361566 : Nat := 118140960795 + 361566 * 2 ^ 59
def prefixEnd_361566 : Nat := 4983230072969 + 3 ^ 40 * 361566 * 2
def baseEnd_361566 : Nat := 110019049673266728925745

theorem tailTrace_361566 : CollatzResearch.WordTrace tailWord_361566 prefixEnd_361566 110019049673266728925745 := by
  unfold tailWord_361566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648424426014450925212069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8791596938743738267797701 1648424426014450925212069)
  ·
    refine ⟨309079579877709548477263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1648424426014450925212069 309079579877709548477263)
    ·
      refine ⟨463619369816564322715895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309079579877709548477263 463619369816564322715895)
      ·
        refine ⟨695429054724846484073843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463619369816564322715895 695429054724846484073843)
        ·
          refine ⟨1043143582087269726110765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695429054724846484073843 1043143582087269726110765)
          ·
            refine ⟨391178843282726147291537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1043143582087269726110765 391178843282726147291537)
            ·
              refine ⟨293384132462044610468653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391178843282726147291537 293384132462044610468653)
              ·
                refine ⟨110019049673266728925745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293384132462044610468653 110019049673266728925745)
                ·
                  rfl

theorem cell19_361566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_361566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361566 prefixEnd_361566 := by exact prefixLift 361566
  have htrace : WordTrace (prefixWord ++ tailWord_361566) baseStart_361566 baseEnd_361566 := by
    simpa [prefixWord, tailWord_361566, baseEnd_361566] using wordTrace_append hprefix tailTrace_361566
  have hstable : (prefixWord ++ tailWord_361566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361566).length < 2 ^ (prefixWord ++ tailWord_361566).sum := by decide
  have hdescent : baseEnd_361566 < baseStart_361566 := by decide
  rcases family_descends (prefixWord ++ tailWord_361566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361570 : List Nat := [3, 3, 2, 2, 1, 1, 4, 3]
def baseStart_361570 : Nat := 118140960795 + 361570 * 2 ^ 59
def prefixEnd_361570 : Nat := 4983230072969 + 3 ^ 40 * 361570 * 2
def baseEnd_361570 : Nat := 110020266812595904836845

theorem tailTrace_361570 : CollatzResearch.WordTrace tailWord_361570 prefixEnd_361570 110020266812595904836845 := by
  unfold tailWord_361570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296885325025279021210541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8791694200067410723228109 3296885325025279021210541)
  ·
    refine ⟨1236331996884479632953953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3296885325025279021210541 1236331996884479632953953)
    ·
      refine ⟨927248997663359724715465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1236331996884479632953953 927248997663359724715465)
      ·
        refine ⟨695436748247519793536599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 927248997663359724715465 695436748247519793536599)
        ·
          refine ⟨1043155122371279690304899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695436748247519793536599 1043155122371279690304899)
          ·
            refine ⟨1564732683556919535457349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043155122371279690304899 1564732683556919535457349)
            ·
              refine ⟨293387378166922412898253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1564732683556919535457349 293387378166922412898253)
              ·
                refine ⟨110020266812595904836845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293387378166922412898253 110020266812595904836845)
                ·
                  rfl

theorem cell19_361570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_361570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361570 prefixEnd_361570 := by exact prefixLift 361570
  have htrace : WordTrace (prefixWord ++ tailWord_361570) baseStart_361570 baseEnd_361570 := by
    simpa [prefixWord, tailWord_361570, baseEnd_361570] using wordTrace_append hprefix tailTrace_361570
  have hstable : (prefixWord ++ tailWord_361570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361570).length < 2 ^ (prefixWord ++ tailWord_361570).sum := by decide
  have hdescent : baseEnd_361570 < baseStart_361570 := by decide
  rcases family_descends (prefixWord ++ tailWord_361570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361589 : List Nat := [1, 3, 4, 3, 1, 2, 5]
def baseStart_361589 : Nat := 118140960795 + 361589 * 2 ^ 59
def prefixEnd_361589 : Nat := 4983230072969 + 3 ^ 40 * 361589 * 2
def baseEnd_361589 : Nat := 36675349408136496804857

theorem tailTrace_361589 : CollatzResearch.WordTrace tailWord_361589 prefixEnd_361589 36675349408136496804857 := by
  unfold tailWord_361589
  simp only [CollatzResearch.WordTrace]
  refine ⟨13188234287032282329783821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8792156191354854886522547 13188234287032282329783821)
  ·
    refine ⟨4945587857637105873668933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13188234287032282329783821 4945587857637105873668933)
    ·
      refine ⟨927297723306957351312925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4945587857637105873668933 927297723306957351312925)
      ·
        refine ⟨347736646240109006742347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 927297723306957351312925 347736646240109006742347)
        ·
          refine ⟨521604969360163510113521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347736646240109006742347 521604969360163510113521)
          ·
            refine ⟨391203727020122632585141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521604969360163510113521 391203727020122632585141)
            ·
              refine ⟨36675349408136496804857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 391203727020122632585141 36675349408136496804857)
              ·
                rfl

theorem cell19_361589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_361589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361589 prefixEnd_361589 := by exact prefixLift 361589
  have htrace : WordTrace (prefixWord ++ tailWord_361589) baseStart_361589 baseEnd_361589 := by
    simpa [prefixWord, tailWord_361589, baseEnd_361589] using wordTrace_append hprefix tailTrace_361589
  have hstable : (prefixWord ++ tailWord_361589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361589).length < 2 ^ (prefixWord ++ tailWord_361589).sum := by decide
  have hdescent : baseEnd_361589 < baseStart_361589 := by decide
  rcases family_descends (prefixWord ++ tailWord_361589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361665 : List Nat := [1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_361665 : Nat := 118140960795 + 361665 * 2 ^ 59
def prefixEnd_361665 : Nat := 4983230072969 + 3 ^ 40 * 361665 * 2
def baseEnd_361665 : Nat := 110049173871663832725475

theorem tailTrace_361665 : CollatzResearch.WordTrace tailWord_361665 prefixEnd_361665 110049173871663832725475 := by
  unfold tailWord_361665
  simp only [CollatzResearch.WordTrace]
  refine ⟨13191006234756947309550449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8794004156504631539700299 13191006234756947309550449)
  ·
    refine ⟨9893254676067710482162837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13191006234756947309550449 9893254676067710482162837)
    ·
      refine ⟨463746312940673928851383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9893254676067710482162837 463746312940673928851383)
      ·
        refine ⟨695619469411010893277075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463746312940673928851383 695619469411010893277075)
        ·
          refine ⟨1043429204116516339915613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695619469411010893277075 1043429204116516339915613)
          ·
            refine ⟨391285951543693627468355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1043429204116516339915613 391285951543693627468355)
            ·
              refine ⟨586928927315540441202533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391285951543693627468355 586928927315540441202533)
              ·
                refine ⟨110049173871663832725475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586928927315540441202533 110049173871663832725475)
                ·
                  rfl

theorem cell19_361665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_361665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361665 prefixEnd_361665 := by exact prefixLift 361665
  have htrace : WordTrace (prefixWord ++ tailWord_361665) baseStart_361665 baseEnd_361665 := by
    simpa [prefixWord, tailWord_361665, baseEnd_361665] using wordTrace_append hprefix tailTrace_361665
  have hstable : (prefixWord ++ tailWord_361665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361665).length < 2 ^ (prefixWord ++ tailWord_361665).sum := by decide
  have hdescent : baseEnd_361665 < baseStart_361665 := by decide
  rcases family_descends (prefixWord ++ tailWord_361665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361728 : List Nat := [2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_361728 : Nat := 118140960795 + 361728 * 2 ^ 59
def prefixEnd_361728 : Nat := 4983230072969 + 3 ^ 40 * 361728 * 2
def baseEnd_361728 : Nat := 110068343816098353325303

theorem tailTrace_361728 : CollatzResearch.WordTrace tailWord_361728 prefixEnd_361728 110068343816098353325303 := by
  unfold tailWord_361728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6596652016764354534546919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8795536022352472712729225 6596652016764354534546919)
  ·
    refine ⟨9894978025146531801820379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6596652016764354534546919 9894978025146531801820379)
    ·
      refine ⟨14842467037719797702730569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9894978025146531801820379 14842467037719797702730569)
      ·
        refine ⟨11131850278289848277047927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14842467037719797702730569 11131850278289848277047927)
        ·
          refine ⟨16697775417434772415571891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11131850278289848277047927 16697775417434772415571891)
          ·
            refine ⟨25046663126152158623357837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16697775417434772415571891 25046663126152158623357837)
            ·
              refine ⟨9392498672307059483759189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25046663126152158623357837 9392498672307059483759189)
              ·
                refine ⟨110068343816098353325303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9392498672307059483759189 110068343816098353325303)
                ·
                  rfl

theorem cell19_361728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_361728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361728 prefixEnd_361728 := by exact prefixLift 361728
  have htrace : WordTrace (prefixWord ++ tailWord_361728) baseStart_361728 baseEnd_361728 := by
    simpa [prefixWord, tailWord_361728, baseEnd_361728] using wordTrace_append hprefix tailTrace_361728
  have hstable : (prefixWord ++ tailWord_361728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361728).length < 2 ^ (prefixWord ++ tailWord_361728).sum := by decide
  have hdescent : baseEnd_361728 < baseStart_361728 := by decide
  rcases family_descends (prefixWord ++ tailWord_361728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361758 : List Nat := [4, 3, 2, 1, 3, 1, 5]
def baseStart_361758 : Nat := 118140960795 + 361758 * 2 ^ 59
def prefixEnd_361758 : Nat := 4983230072969 + 3 ^ 40 * 361758 * 2
def baseEnd_361758 : Nat := 36692490787022390886185

theorem tailTrace_361758 : CollatzResearch.WordTrace tailWord_361758 prefixEnd_361758 36692490787022390886185 := by
  unfold tailWord_361758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649299777927503024085741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8796265482280016128457285 1649299777927503024085741)
  ·
    refine ⟨618487416722813634032153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1649299777927503024085741 618487416722813634032153)
    ·
      refine ⟨463865562542110225524115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 618487416722813634032153 463865562542110225524115)
      ·
        refine ⟨695798343813165338286173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463865562542110225524115 695798343813165338286173)
        ·
          refine ⟨260924378929937001857315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 695798343813165338286173 260924378929937001857315)
          ·
            refine ⟨391386568394905502785973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260924378929937001857315 391386568394905502785973)
            ·
              refine ⟨36692490787022390886185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 391386568394905502785973 36692490787022390886185)
              ·
                rfl

theorem cell19_361758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 5].length) (baseStart_361758 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361758 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361758 prefixEnd_361758 := by exact prefixLift 361758
  have htrace : WordTrace (prefixWord ++ tailWord_361758) baseStart_361758 baseEnd_361758 := by
    simpa [prefixWord, tailWord_361758, baseEnd_361758] using wordTrace_append hprefix tailTrace_361758
  have hstable : (prefixWord ++ tailWord_361758).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361758).length < 2 ^ (prefixWord ++ tailWord_361758).sum := by decide
  have hdescent : baseEnd_361758 < baseStart_361758 := by decide
  rcases family_descends (prefixWord ++ tailWord_361758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361762 : List Nat := [3, 3, 1, 1, 4, 2, 5]
def baseStart_361762 : Nat := 118140960795 + 361762 * 2 ^ 59
def prefixEnd_361762 : Nat := 4983230072969 + 3 ^ 40 * 361762 * 2
def baseEnd_361762 : Nat := 36692896500132116189885

theorem tailTrace_361762 : CollatzResearch.WordTrace tailWord_361762 prefixEnd_361762 36692896500132116189885 := by
  unfold tailWord_361762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298636028851383218957885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8796362743603688583887693 3298636028851383218957885)
  ·
    refine ⟨1236988510819268707109207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3298636028851383218957885 1236988510819268707109207)
    ·
      refine ⟨1855482766228903060663811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236988510819268707109207 1855482766228903060663811)
      ·
        refine ⟨2783224149343354590995717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855482766228903060663811 2783224149343354590995717)
        ·
          refine ⟨521854528001878985811697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2783224149343354590995717 521854528001878985811697)
          ·
            refine ⟨391390896001409239358773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521854528001878985811697 391390896001409239358773)
            ·
              refine ⟨36692896500132116189885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 391390896001409239358773 36692896500132116189885)
              ·
                rfl

theorem cell19_361762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_361762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361762 prefixEnd_361762 := by exact prefixLift 361762
  have htrace : WordTrace (prefixWord ++ tailWord_361762) baseStart_361762 baseEnd_361762 := by
    simpa [prefixWord, tailWord_361762, baseEnd_361762] using wordTrace_append hprefix tailTrace_361762
  have hstable : (prefixWord ++ tailWord_361762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361762).length < 2 ^ (prefixWord ++ tailWord_361762).sum := by decide
  have hdescent : baseEnd_361762 < baseStart_361762 := by decide
  rcases family_descends (prefixWord ++ tailWord_361762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361861 : List Nat := [1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_361861 : Nat := 118140960795 + 361861 * 2 ^ 59
def prefixEnd_361861 : Nat := 4983230072969 + 3 ^ 40 * 361861 * 2
def baseEnd_361861 : Nat := 110108813698793452369385

theorem tailTrace_361861 : CollatzResearch.WordTrace tailWord_361861 prefixEnd_361861 110108813698793452369385 := by
  unfold tailWord_361861
  simp only [CollatzResearch.WordTrace]
  refine ⟨13198154942046872783685437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8798769961364581855790291 13198154942046872783685437)
  ·
    refine ⟨4949308103267577293882039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13198154942046872783685437 4949308103267577293882039)
    ·
      refine ⟨7423962154901365940823059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4949308103267577293882039 7423962154901365940823059)
      ·
        refine ⟨11135943232352048911234589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7423962154901365940823059 11135943232352048911234589)
        ·
          refine ⟨4175978712132018341712971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11135943232352048911234589 4175978712132018341712971)
          ·
            refine ⟨6263968068198027512569457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175978712132018341712971 6263968068198027512569457)
            ·
              refine ⟨4697976051148520634427093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6263968068198027512569457 4697976051148520634427093)
              ·
                refine ⟨110108813698793452369385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4697976051148520634427093 110108813698793452369385)
                ·
                  rfl

theorem cell19_361861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_361861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361861 prefixEnd_361861 := by exact prefixLift 361861
  have htrace : WordTrace (prefixWord ++ tailWord_361861) baseStart_361861 baseEnd_361861 := by
    simpa [prefixWord, tailWord_361861, baseEnd_361861] using wordTrace_append hprefix tailTrace_361861
  have hstable : (prefixWord ++ tailWord_361861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361861).length < 2 ^ (prefixWord ++ tailWord_361861).sum := by decide
  have hdescent : baseEnd_361861 < baseStart_361861 := by decide
  rcases family_descends (prefixWord ++ tailWord_361861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361994 : List Nat := [3, 1, 2, 2, 2, 9]
def baseStart_361994 : Nat := 118140960795 + 361994 * 2 ^ 59
def prefixEnd_361994 : Nat := 4983230072969 + 3 ^ 40 * 361994 * 2
def baseEnd_361994 : Nat := 12238809286832061268163

theorem tailTrace_361994 : CollatzResearch.WordTrace tailWord_361994 prefixEnd_361994 12238809286832061268163 := by
  unfold tailWord_361994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300751462641259124569259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8802003900376690998851357 3300751462641259124569259)
  ·
    refine ⟨4951127193961888686853889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3300751462641259124569259 4951127193961888686853889)
    ·
      refine ⟨3713345395471416515140417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4951127193961888686853889 3713345395471416515140417)
      ·
        refine ⟨2785009046603562386355313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3713345395471416515140417 2785009046603562386355313)
        ·
          refine ⟨2088756784952671789766485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2785009046603562386355313 2088756784952671789766485)
          ·
            refine ⟨12238809286832061268163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2088756784952671789766485 12238809286832061268163)
            ·
              rfl

theorem cell19_361994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 9].length) (baseStart_361994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361994 prefixEnd_361994 := by exact prefixLift 361994
  have htrace : WordTrace (prefixWord ++ tailWord_361994) baseStart_361994 baseEnd_361994 := by
    simpa [prefixWord, tailWord_361994, baseEnd_361994] using wordTrace_append hprefix tailTrace_361994
  have hstable : (prefixWord ++ tailWord_361994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361994).length < 2 ^ (prefixWord ++ tailWord_361994).sum := by decide
  have hdescent : baseEnd_361994 < baseStart_361994 := by decide
  rcases family_descends (prefixWord ++ tailWord_361994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362085 : List Nat := [1, 3, 1, 3, 3, 3, 2, 3]
def baseStart_362085 : Nat := 118140960795 + 362085 * 2 ^ 59
def prefixEnd_362085 : Nat := 4983230072969 + 3 ^ 40 * 362085 * 2
def baseEnd_362085 : Nat := 110176973501227303390997

theorem tailTrace_362085 : CollatzResearch.WordTrace tailWord_362085 prefixEnd_362085 110176973501227303390997 := by
  unfold tailWord_362085
  simp only [CollatzResearch.WordTrace]
  refine ⟨13206324893235359039839709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8804216595490239359893139 13206324893235359039839709)
  ·
    refine ⟨4952371834963259639939891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13206324893235359039839709 4952371834963259639939891)
    ·
      refine ⟨7428557752444889459909837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4952371834963259639939891 7428557752444889459909837)
      ·
        refine ⟨2785709157166833547466189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7428557752444889459909837 2785709157166833547466189)
        ·
          refine ⟨1044640933937562580299821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2785709157166833547466189 1044640933937562580299821)
          ·
            refine ⟨391740350226585967612433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1044640933937562580299821 391740350226585967612433)
            ·
              refine ⟨293805262669939475709325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391740350226585967612433 293805262669939475709325)
              ·
                refine ⟨110176973501227303390997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293805262669939475709325 110176973501227303390997)
                ·
                  rfl

theorem cell19_362085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_362085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362085 prefixEnd_362085 := by exact prefixLift 362085
  have htrace : WordTrace (prefixWord ++ tailWord_362085) baseStart_362085 baseEnd_362085 := by
    simpa [prefixWord, tailWord_362085, baseEnd_362085] using wordTrace_append hprefix tailTrace_362085
  have hstable : (prefixWord ++ tailWord_362085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362085).length < 2 ^ (prefixWord ++ tailWord_362085).sum := by decide
  have hdescent : baseEnd_362085 < baseStart_362085 := by decide
  rcases family_descends (prefixWord ++ tailWord_362085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362087 : List Nat := [1, 1, 5, 1, 1, 1, 6, 3]
def baseStart_362087 : Nat := 118140960795 + 362087 * 2 ^ 59
def prefixEnd_362087 : Nat := 4983230072969 + 3 ^ 40 * 362087 * 2
def baseEnd_362087 : Nat := 110177582070891891346547

theorem tailTrace_362087 : CollatzResearch.WordTrace tailWord_362087 prefixEnd_362087 110177582070891891346547 := by
  unfold tailWord_362087
  simp only [CollatzResearch.WordTrace]
  refine ⟨13206397839228113381412515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8804265226152075587608343 13206397839228113381412515)
  ·
    refine ⟨19809596758842170072118773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13206397839228113381412515 19809596758842170072118773)
    ·
      refine ⟨1857149696141453444261135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19809596758842170072118773 1857149696141453444261135)
      ·
        refine ⟨2785724544212180166391703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857149696141453444261135 2785724544212180166391703)
        ·
          refine ⟨4178586816318270249587555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785724544212180166391703 4178586816318270249587555)
          ·
            refine ⟨6267880224477405374381333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178586816318270249587555 6267880224477405374381333)
            ·
              refine ⟨293806885522378376924125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6267880224477405374381333 293806885522378376924125)
              ·
                refine ⟨110177582070891891346547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293806885522378376924125 110177582070891891346547)
                ·
                  rfl

theorem cell19_362087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_362087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362087 prefixEnd_362087 := by exact prefixLift 362087
  have htrace : WordTrace (prefixWord ++ tailWord_362087) baseStart_362087 baseEnd_362087 := by
    simpa [prefixWord, tailWord_362087, baseEnd_362087] using wordTrace_append hprefix tailTrace_362087
  have hstable : (prefixWord ++ tailWord_362087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362087).length < 2 ^ (prefixWord ++ tailWord_362087).sum := by decide
  have hdescent : baseEnd_362087 < baseStart_362087 := by decide
  rcases family_descends (prefixWord ++ tailWord_362087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362165 : List Nat := [1, 3, 3, 3, 9]
def baseStart_362165 : Nat := 118140960795 + 362165 * 2 ^ 59
def prefixEnd_362165 : Nat := 4983230072969 + 3 ^ 40 * 362165 * 2
def baseEnd_362165 : Nat := 4081530232881882281963

theorem tailTrace_362165 : CollatzResearch.WordTrace tailWord_362165 prefixEnd_362165 4081530232881882281963 := by
  unfold tailWord_362165
  simp only [CollatzResearch.WordTrace]
  refine ⟨13209242732945532702751949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8806161821963688468501299 13209242732945532702751949)
  ·
    refine ⟨4953466024854574763531981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13209242732945532702751949 4953466024854574763531981)
    ·
      refine ⟨1857549759320465536324493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4953466024854574763531981 1857549759320465536324493)
      ·
        refine ⟨696581159745174576121685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1857549759320465536324493 696581159745174576121685)
        ·
          refine ⟨4081530232881882281963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 696581159745174576121685 4081530232881882281963)
          ·
            rfl

theorem cell19_362165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 9].length) (baseStart_362165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362165 prefixEnd_362165 := by exact prefixLift 362165
  have htrace : WordTrace (prefixWord ++ tailWord_362165) baseStart_362165 baseEnd_362165 := by
    simpa [prefixWord, tailWord_362165, baseEnd_362165] using wordTrace_append hprefix tailTrace_362165
  have hstable : (prefixWord ++ tailWord_362165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362165).length < 2 ^ (prefixWord ++ tailWord_362165).sum := by decide
  have hdescent : baseEnd_362165 < baseStart_362165 := by decide
  rcases family_descends (prefixWord ++ tailWord_362165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362201 : List Nat := [1, 2, 1, 2, 3, 4, 3, 3]
def baseStart_362201 : Nat := 118140960795 + 362201 * 2 ^ 59
def prefixEnd_362201 : Nat := 4983230072969 + 3 ^ 40 * 362201 * 2
def baseEnd_362201 : Nat := 110212270541773404812903

theorem tailTrace_362201 : CollatzResearch.WordTrace tailWord_362201 prefixEnd_362201 110212270541773404812903 := by
  unfold tailWord_362201
  simp only [CollatzResearch.WordTrace]
  refine ⟨13210555760815110851062457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8807037173876740567374971 13210555760815110851062457)
  ·
    refine ⟨9907916820611333138296843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13210555760815110851062457 9907916820611333138296843)
    ·
      refine ⟨14861875230916999707445265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9907916820611333138296843 14861875230916999707445265)
      ·
        refine ⟨11146406423187749780583949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14861875230916999707445265 11146406423187749780583949)
        ·
          refine ⟨4179902408695406167718981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11146406423187749780583949 4179902408695406167718981)
          ·
            refine ⟨783731701630388656447309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4179902408695406167718981 783731701630388656447309)
            ·
              refine ⟨293899388111395746167741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 783731701630388656447309 293899388111395746167741)
              ·
                refine ⟨110212270541773404812903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293899388111395746167741 110212270541773404812903)
                ·
                  rfl

theorem cell19_362201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_362201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362201 prefixEnd_362201 := by exact prefixLift 362201
  have htrace : WordTrace (prefixWord ++ tailWord_362201) baseStart_362201 baseEnd_362201 := by
    simpa [prefixWord, tailWord_362201, baseEnd_362201] using wordTrace_append hprefix tailTrace_362201
  have hstable : (prefixWord ++ tailWord_362201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362201).length < 2 ^ (prefixWord ++ tailWord_362201).sum := by decide
  have hdescent : baseEnd_362201 < baseStart_362201 := by decide
  rcases family_descends (prefixWord ++ tailWord_362201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362222 : List Nat := [4, 1, 2, 1, 1, 2, 8]
def baseStart_362222 : Nat := 118140960795 + 362222 * 2 ^ 59
def prefixEnd_362222 : Nat := 4983230072969 + 3 ^ 40 * 362222 * 2
def baseEnd_362222 : Nat := 36739553507750526115393

theorem tailTrace_362222 : CollatzResearch.WordTrace tailWord_362222 prefixEnd_362222 36739553507750526115393 := by
  unfold tailWord_362222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651415211717378929697115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8807547795826020958384613 1651415211717378929697115)
  ·
    refine ⟨2477122817576068394545673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1651415211717378929697115 2477122817576068394545673)
    ·
      refine ⟨1857842113182051295909255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2477122817576068394545673 1857842113182051295909255)
      ·
        refine ⟨2786763169773076943863883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857842113182051295909255 2786763169773076943863883)
        ·
          refine ⟨4180144754659615415795825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786763169773076943863883 4180144754659615415795825)
          ·
            refine ⟨3135108565994711561846869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4180144754659615415795825 3135108565994711561846869)
            ·
              refine ⟨36739553507750526115393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3135108565994711561846869 36739553507750526115393)
              ·
                rfl

theorem cell19_362222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_362222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362222 prefixEnd_362222 := by exact prefixLift 362222
  have htrace : WordTrace (prefixWord ++ tailWord_362222) baseStart_362222 baseEnd_362222 := by
    simpa [prefixWord, tailWord_362222, baseEnd_362222] using wordTrace_append hprefix tailTrace_362222
  have hstable : (prefixWord ++ tailWord_362222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362222).length < 2 ^ (prefixWord ++ tailWord_362222).sum := by decide
  have hdescent : baseEnd_362222 < baseStart_362222 := by decide
  rcases family_descends (prefixWord ++ tailWord_362222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362246 : List Nat := [6, 2, 2, 1, 2, 1, 2, 3]
def baseStart_362246 : Nat := 118140960795 + 362246 * 2 ^ 59
def prefixEnd_362246 : Nat := 4983230072969 + 3 ^ 40 * 362246 * 2
def baseEnd_362246 : Nat := 110225963359226633812781

theorem tailTrace_362246 : CollatzResearch.WordTrace tailWord_362246 prefixEnd_362246 110225963359226633812781 := by
  unfold tailWord_362246
  simp only [CollatzResearch.WordTrace]
  refine ⟨412881157676627610514081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8808131363768055690967061 412881157676627610514081)
  ·
    refine ⟨309660868257470707885561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 412881157676627610514081 309660868257470707885561)
    ·
      refine ⟨232245651193103030914171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309660868257470707885561 232245651193103030914171)
      ·
        refine ⟨348368476789654546371257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232245651193103030914171 348368476789654546371257)
        ·
          refine ⟨261276357592240909778443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348368476789654546371257 261276357592240909778443)
          ·
            refine ⟨391914536388361364667665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261276357592240909778443 391914536388361364667665)
            ·
              refine ⟨293935902291271023500749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391914536388361364667665 293935902291271023500749)
              ·
                refine ⟨110225963359226633812781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293935902291271023500749 110225963359226633812781)
                ·
                  rfl

theorem cell19_362246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_362246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362246 prefixEnd_362246 := by exact prefixLift 362246
  have htrace : WordTrace (prefixWord ++ tailWord_362246) baseStart_362246 baseEnd_362246 := by
    simpa [prefixWord, tailWord_362246, baseEnd_362246] using wordTrace_append hprefix tailTrace_362246
  have hstable : (prefixWord ++ tailWord_362246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362246).length < 2 ^ (prefixWord ++ tailWord_362246).sum := by decide
  have hdescent : baseEnd_362246 < baseStart_362246 := by decide
  rcases family_descends (prefixWord ++ tailWord_362246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362294 : List Nat := [5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_362294 : Nat := 118140960795 + 362294 * 2 ^ 59
def prefixEnd_362294 : Nat := 4983230072969 + 3 ^ 40 * 362294 * 2
def baseEnd_362294 : Nat := 110240569031176744745983

theorem tailTrace_362294 : CollatzResearch.WordTrace tailWord_362294 prefixEnd_362294 110240569031176744745983 := by
  unfold tailWord_362294
  simp only [CollatzResearch.WordTrace]
  refine ⟨825871734342386733387371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8809298499652125156131957 825871734342386733387371)
  ·
    refine ⟨1238807601513580100081057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 825871734342386733387371 1238807601513580100081057)
    ·
      refine ⟨929105701135185075060793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1238807601513580100081057 929105701135185075060793)
      ·
        refine ⟨696829275851388806295595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 929105701135185075060793 696829275851388806295595)
        ·
          refine ⟨1045243913777083209443393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696829275851388806295595 1045243913777083209443393)
          ·
            refine ⟨783932935332812407082545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1045243913777083209443393 783932935332812407082545)
            ·
              refine ⟨587949701499609305311909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783932935332812407082545 587949701499609305311909)
              ·
                refine ⟨110240569031176744745983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 587949701499609305311909 110240569031176744745983)
                ·
                  rfl

theorem cell19_362294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_362294 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362294 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362294 prefixEnd_362294 := by exact prefixLift 362294
  have htrace : WordTrace (prefixWord ++ tailWord_362294) baseStart_362294 baseEnd_362294 := by
    simpa [prefixWord, tailWord_362294, baseEnd_362294] using wordTrace_append hprefix tailTrace_362294
  have hstable : (prefixWord ++ tailWord_362294).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362294).length < 2 ^ (prefixWord ++ tailWord_362294).sum := by decide
  have hdescent : baseEnd_362294 < baseStart_362294 := by decide
  rcases family_descends (prefixWord ++ tailWord_362294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362298 : List Nat := [3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_362298 : Nat := 118140960795 + 362298 * 2 ^ 59
def prefixEnd_362298 : Nat := 4983230072969 + 3 ^ 40 * 362298 * 2
def baseEnd_362298 : Nat := 110241786170505920657083

theorem tailTrace_362298 : CollatzResearch.WordTrace tailWord_362298 prefixEnd_362298 110241786170505920657083 := by
  unfold tailWord_362298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3303523410365924104335887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8809395760975797611562365 3303523410365924104335887)
  ·
    refine ⟨4955285115548886156503831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3303523410365924104335887 4955285115548886156503831)
    ·
      refine ⟨7432927673323329234755747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4955285115548886156503831 7432927673323329234755747)
      ·
        refine ⟨11149391509984993852133621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7432927673323329234755747 11149391509984993852133621)
        ·
          refine ⟨1045255454061093173637527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11149391509984993852133621 1045255454061093173637527)
          ·
            refine ⟨1567883181091639760456291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045255454061093173637527 1567883181091639760456291)
            ·
              refine ⟨2351824771637459640684437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567883181091639760456291 2351824771637459640684437)
              ·
                refine ⟨110241786170505920657083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2351824771637459640684437 110241786170505920657083)
                ·
                  rfl

theorem cell19_362298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_362298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362298 prefixEnd_362298 := by exact prefixLift 362298
  have htrace : WordTrace (prefixWord ++ tailWord_362298) baseStart_362298 baseEnd_362298 := by
    simpa [prefixWord, tailWord_362298, baseEnd_362298] using wordTrace_append hprefix tailTrace_362298
  have hstable : (prefixWord ++ tailWord_362298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362298).length < 2 ^ (prefixWord ++ tailWord_362298).sum := by decide
  have hdescent : baseEnd_362298 < baseStart_362298 := by decide
  rcases family_descends (prefixWord ++ tailWord_362298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362429 : List Nat := [1, 4, 1, 2, 3, 1, 4, 3]
def baseStart_362429 : Nat := 118140960795 + 362429 * 2 ^ 59
def prefixEnd_362429 : Nat := 4983230072969 + 3 ^ 40 * 362429 * 2
def baseEnd_362429 : Nat := 110281647483536431745615

theorem tailTrace_362429 : CollatzResearch.WordTrace tailWord_362429 prefixEnd_362429 110281647483536431745615 := by
  unfold tailWord_362429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13218871603989105790362341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8812581069326070526908227 13218871603989105790362341)
  ·
    refine ⟨2478538425747957335692939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13218871603989105790362341 2478538425747957335692939)
    ·
      refine ⟨3717807638621936003539409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478538425747957335692939 3717807638621936003539409)
      ·
        refine ⟨2788355728966452002654557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3717807638621936003539409 2788355728966452002654557)
        ·
          refine ⟨1045633398362419500995459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2788355728966452002654557 1045633398362419500995459)
          ·
            refine ⟨1568450097543629251493189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045633398362419500995459 1568450097543629251493189)
            ·
              refine ⟨294084393289430484654973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1568450097543629251493189 294084393289430484654973)
              ·
                refine ⟨110281647483536431745615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294084393289430484654973 110281647483536431745615)
                ·
                  rfl

theorem cell19_362429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_362429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362429 prefixEnd_362429 := by exact prefixLift 362429
  have htrace : WordTrace (prefixWord ++ tailWord_362429) baseStart_362429 baseEnd_362429 := by
    simpa [prefixWord, tailWord_362429, baseEnd_362429] using wordTrace_append hprefix tailTrace_362429
  have hstable : (prefixWord ++ tailWord_362429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362429).length < 2 ^ (prefixWord ++ tailWord_362429).sum := by decide
  have hdescent : baseEnd_362429 < baseStart_362429 := by decide
  rcases family_descends (prefixWord ++ tailWord_362429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362524 : List Nat := [2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_362524 : Nat := 118140960795 + 362524 * 2 ^ 59
def prefixEnd_362524 : Nat := 4983230072969 + 3 ^ 40 * 362524 * 2
def baseEnd_362524 : Nat := 110310554542604359634245

theorem tailTrace_362524 : CollatzResearch.WordTrace tailWord_362524 prefixEnd_362524 110310554542604359634245 := by
  unfold tailWord_362524
  simp only [CollatzResearch.WordTrace]
  refine ⟨6611168269322468507535313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8814891025763291343380417 6611168269322468507535313)
  ·
    refine ⟨4958376201991851380651485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6611168269322468507535313 4958376201991851380651485)
    ·
      refine ⟨1859391075746944267744307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4958376201991851380651485 1859391075746944267744307)
      ·
        refine ⟨2789086613620416401616461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859391075746944267744307 2789086613620416401616461)
        ·
          refine ⟨1045907480107656150606173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2789086613620416401616461 1045907480107656150606173)
          ·
            refine ⟨392215305040371056477315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1045907480107656150606173 392215305040371056477315)
            ·
              refine ⟨588322957560556584715973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392215305040371056477315 588322957560556584715973)
              ·
                refine ⟨110310554542604359634245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 588322957560556584715973 110310554542604359634245)
                ·
                  rfl

theorem cell19_362524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_362524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362524 prefixEnd_362524 := by exact prefixLift 362524
  have htrace : WordTrace (prefixWord ++ tailWord_362524) baseStart_362524 baseEnd_362524 := by
    simpa [prefixWord, tailWord_362524, baseEnd_362524] using wordTrace_append hprefix tailTrace_362524
  have hstable : (prefixWord ++ tailWord_362524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362524).length < 2 ^ (prefixWord ++ tailWord_362524).sum := by decide
  have hdescent : baseEnd_362524 < baseStart_362524 := by decide
  rcases family_descends (prefixWord ++ tailWord_362524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362547 : List Nat := [1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_362547 : Nat := 118140960795 + 362547 * 2 ^ 59
def prefixEnd_362547 : Nat := 4983230072969 + 3 ^ 40 * 362547 * 2
def baseEnd_362547 : Nat := 110317553093747121123071

theorem tailTrace_362547 : CollatzResearch.WordTrace tailWord_362547 prefixEnd_362547 110317553093747121123071 := by
  unfold tailWord_362547
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223175417561611943157895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8815450278374407962105263 13223175417561611943157895)
  ·
    refine ⟨19834763126342417914736843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13223175417561611943157895 19834763126342417914736843)
    ·
      refine ⟨29752144689513626872105265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19834763126342417914736843 29752144689513626872105265)
      ·
        refine ⟨22314108517135220154078949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29752144689513626872105265 22314108517135220154078949)
        ·
          refine ⟨4183895346962853778889803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22314108517135220154078949 4183895346962853778889803)
          ·
            refine ⟨6275843020444280668334705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4183895346962853778889803 6275843020444280668334705)
            ·
              refine ⟨4706882265333210501251029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6275843020444280668334705 4706882265333210501251029)
              ·
                refine ⟨110317553093747121123071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4706882265333210501251029 110317553093747121123071)
                ·
                  rfl

theorem cell19_362547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_362547 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362547 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362547 prefixEnd_362547 := by exact prefixLift 362547
  have htrace : WordTrace (prefixWord ++ tailWord_362547) baseStart_362547 baseEnd_362547 := by
    simpa [prefixWord, tailWord_362547, baseEnd_362547] using wordTrace_append hprefix tailTrace_362547
  have hstable : (prefixWord ++ tailWord_362547).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362547).length < 2 ^ (prefixWord ++ tailWord_362547).sum := by decide
  have hdescent : baseEnd_362547 < baseStart_362547 := by decide
  rcases family_descends (prefixWord ++ tailWord_362547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362585 : List Nat := [1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_362585 : Nat := 118140960795 + 362585 * 2 ^ 59
def prefixEnd_362585 : Nat := 4983230072969 + 3 ^ 40 * 362585 * 2
def baseEnd_362585 : Nat := 110329115917374292278523

theorem tailTrace_362585 : CollatzResearch.WordTrace tailWord_362585 prefixEnd_362585 110329115917374292278523 := by
  unfold tailWord_362585
  simp only [CollatzResearch.WordTrace]
  refine ⟨13224561391423944433041209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8816374260949296288694139 13224561391423944433041209)
  ·
    refine ⟨9918421043567958324780907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13224561391423944433041209 9918421043567958324780907)
    ·
      refine ⟨14877631565351937487171361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9918421043567958324780907 14877631565351937487171361)
      ·
        refine ⟨11158223674013953115378521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14877631565351937487171361 11158223674013953115378521)
        ·
          refine ⟨8368667755510464836533891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11158223674013953115378521 8368667755510464836533891)
          ·
            refine ⟨12553001633265697254800837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8368667755510464836533891 12553001633265697254800837)
            ·
              refine ⟨2353687806237318235275157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12553001633265697254800837 2353687806237318235275157)
              ·
                refine ⟨110329115917374292278523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2353687806237318235275157 110329115917374292278523)
                ·
                  rfl

theorem cell19_362585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_362585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362585 prefixEnd_362585 := by exact prefixLift 362585
  have htrace : WordTrace (prefixWord ++ tailWord_362585) baseStart_362585 baseEnd_362585 := by
    simpa [prefixWord, tailWord_362585, baseEnd_362585] using wordTrace_append hprefix tailTrace_362585
  have hstable : (prefixWord ++ tailWord_362585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362585).length < 2 ^ (prefixWord ++ tailWord_362585).sum := by decide
  have hdescent : baseEnd_362585 < baseStart_362585 := by decide
  rcases family_descends (prefixWord ++ tailWord_362585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362621 : List Nat := [1, 4, 1, 1, 3, 4, 5]
def baseStart_362621 : Nat := 118140960795 + 362621 * 2 ^ 59
def prefixEnd_362621 : Nat := 4983230072969 + 3 ^ 40 * 362621 * 2
def baseEnd_362621 : Nat := 36780023390445625159475

theorem tailTrace_362621 : CollatzResearch.WordTrace tailWord_362621 prefixEnd_362621 36780023390445625159475 := by
  unfold tailWord_362621
  simp only [CollatzResearch.WordTrace]
  refine ⟨13225874419293522581351717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8817249612862348387567811 13225874419293522581351717)
  ·
    refine ⟨2479851453617535484003447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13225874419293522581351717 2479851453617535484003447)
    ·
      refine ⟨3719777180426303226005171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2479851453617535484003447 3719777180426303226005171)
      ·
        refine ⟨5579665770639454839007757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719777180426303226005171 5579665770639454839007757)
        ·
          refine ⟨2092374663989795564627909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5579665770639454839007757 2092374663989795564627909)
          ·
            refine ⟨392320249498086668367733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2092374663989795564627909 392320249498086668367733)
            ·
              refine ⟨36780023390445625159475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 392320249498086668367733 36780023390445625159475)
              ·
                rfl

theorem cell19_362621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_362621 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362621 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362621 prefixEnd_362621 := by exact prefixLift 362621
  have htrace : WordTrace (prefixWord ++ tailWord_362621) baseStart_362621 baseEnd_362621 := by
    simpa [prefixWord, tailWord_362621, baseEnd_362621] using wordTrace_append hprefix tailTrace_362621
  have hstable : (prefixWord ++ tailWord_362621).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362621).length < 2 ^ (prefixWord ++ tailWord_362621).sum := by decide
  have hdescent : baseEnd_362621 < baseStart_362621 := by decide
  rcases family_descends (prefixWord ++ tailWord_362621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362638 : List Nat := [4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_362638 : Nat := 118140960795 + 362638 * 2 ^ 59
def prefixEnd_362638 : Nat := 4983230072969 + 3 ^ 40 * 362638 * 2
def baseEnd_362638 : Nat := 110345243013485873100601

theorem tailTrace_362638 : CollatzResearch.WordTrace tailWord_362638 prefixEnd_362638 110345243013485873100601 := by
  unfold tailWord_362638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653311807528991810590071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8817662973487956323147045 1653311807528991810590071)
  ·
    refine ⟨2479967711293487715885107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1653311807528991810590071 2479967711293487715885107)
    ·
      refine ⟨3719951566940231573827661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2479967711293487715885107 3719951566940231573827661)
      ·
        refine ⟨1394981837602586840185373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3719951566940231573827661 1394981837602586840185373)
        ·
          refine ⟨523118189100970065069515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1394981837602586840185373 523118189100970065069515)
          ·
            refine ⟨784677283651455097604273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523118189100970065069515 784677283651455097604273)
            ·
              refine ⟨588507962738591323203205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784677283651455097604273 588507962738591323203205)
              ·
                refine ⟨110345243013485873100601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 588507962738591323203205 110345243013485873100601)
                ·
                  rfl

theorem cell19_362638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_362638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362638 prefixEnd_362638 := by exact prefixLift 362638
  have htrace : WordTrace (prefixWord ++ tailWord_362638) baseStart_362638 baseEnd_362638 := by
    simpa [prefixWord, tailWord_362638, baseEnd_362638] using wordTrace_append hprefix tailTrace_362638
  have hstable : (prefixWord ++ tailWord_362638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362638).length < 2 ^ (prefixWord ++ tailWord_362638).sum := by decide
  have hdescent : baseEnd_362638 < baseStart_362638 := by decide
  rcases family_descends (prefixWord ++ tailWord_362638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362661 : List Nat := [1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_362661 : Nat := 118140960795 + 362661 * 2 ^ 59
def prefixEnd_362661 : Nat := 4983230072969 + 3 ^ 40 * 362661 * 2
def baseEnd_362661 : Nat := 110352241564628634589427

theorem tailTrace_362661 : CollatzResearch.WordTrace tailWord_362661 prefixEnd_362661 110352241564628634589427 := by
  unfold tailWord_362661
  simp only [CollatzResearch.WordTrace]
  refine ⟨13227333339148609412807837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8818222226099072941871891 13227333339148609412807837)
  ·
    refine ⟨4960250002180728529802939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13227333339148609412807837 4960250002180728529802939)
    ·
      refine ⟨7440375003271092794704409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4960250002180728529802939 7440375003271092794704409)
      ·
        refine ⟨5580281252453319596028307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7440375003271092794704409 5580281252453319596028307)
        ·
          refine ⟨8370421878679979394042461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580281252453319596028307 8370421878679979394042461)
          ·
            refine ⟨3138908204504992272765923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8370421878679979394042461 3138908204504992272765923)
            ·
              refine ⟨4708362306757488409148885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138908204504992272765923 4708362306757488409148885)
              ·
                refine ⟨110352241564628634589427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4708362306757488409148885 110352241564628634589427)
                ·
                  rfl

theorem cell19_362661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_362661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362661 prefixEnd_362661 := by exact prefixLift 362661
  have htrace : WordTrace (prefixWord ++ tailWord_362661) baseStart_362661 baseEnd_362661 := by
    simpa [prefixWord, tailWord_362661, baseEnd_362661] using wordTrace_append hprefix tailTrace_362661
  have hstable : (prefixWord ++ tailWord_362661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362661).length < 2 ^ (prefixWord ++ tailWord_362661).sum := by decide
  have hdescent : baseEnd_362661 < baseStart_362661 := by decide
  rcases family_descends (prefixWord ++ tailWord_362661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362678 : List Nat := [5, 1, 3, 10]
def baseStart_362678 : Nat := 118140960795 + 362678 * 2 ^ 59
def prefixEnd_362678 : Nat := 4983230072969 + 3 ^ 40 * 362678 * 2
def baseEnd_362678 : Nat := 1362437214898489286563

theorem tailTrace_362678 : CollatzResearch.WordTrace tailWord_362678 prefixEnd_362678 1362437214898489286563 := by
  unfold tailWord_362678
  simp only [CollatzResearch.WordTrace]
  refine ⟨826747086255438832261043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8818635586724680877451125 826747086255438832261043)
  ·
    refine ⟨1240120629383158248391565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826747086255438832261043 1240120629383158248391565)
    ·
      refine ⟨465045236018684343146837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1240120629383158248391565 465045236018684343146837)
      ·
        refine ⟨1362437214898489286563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 465045236018684343146837 1362437214898489286563)
        ·
          rfl

theorem cell19_362678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 10].length) (baseStart_362678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362678 prefixEnd_362678 := by exact prefixLift 362678
  have htrace : WordTrace (prefixWord ++ tailWord_362678) baseStart_362678 baseEnd_362678 := by
    simpa [prefixWord, tailWord_362678, baseEnd_362678] using wordTrace_append hprefix tailTrace_362678
  have hstable : (prefixWord ++ tailWord_362678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362678).length < 2 ^ (prefixWord ++ tailWord_362678).sum := by decide
  have hdescent : baseEnd_362678 < baseStart_362678 := by decide
  rcases family_descends (prefixWord ++ tailWord_362678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362773 : List Nat := [1, 3, 2, 1, 2, 1, 6, 3]
def baseStart_362773 : Nat := 118140960795 + 362773 * 2 ^ 59
def prefixEnd_362773 : Nat := 4983230072969 + 3 ^ 40 * 362773 * 2
def baseEnd_362773 : Nat := 110386321465845560100233

theorem tailTrace_362773 : CollatzResearch.WordTrace tailWord_362773 prefixEnd_362773 110386321465845560100233 := by
  unfold tailWord_362773
  simp only [CollatzResearch.WordTrace]
  refine ⟨13231418314742852540884973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8820945543161901693923315 13231418314742852540884973)
  ·
    refine ⟨4961781868028569702831865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13231418314742852540884973 4961781868028569702831865)
    ·
      refine ⟨3721336401021427277123899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4961781868028569702831865 3721336401021427277123899)
      ·
        refine ⟨5582004601532140915685849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721336401021427277123899 5582004601532140915685849)
        ·
          refine ⟨4186503451149105686764387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5582004601532140915685849 4186503451149105686764387)
          ·
            refine ⟨6279755176723658530146581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186503451149105686764387 6279755176723658530146581)
            ·
              refine ⟨294363523908921493600621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6279755176723658530146581 294363523908921493600621)
              ·
                refine ⟨110386321465845560100233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294363523908921493600621 110386321465845560100233)
                ·
                  rfl

theorem cell19_362773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_362773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362773 prefixEnd_362773 := by exact prefixLift 362773
  have htrace : WordTrace (prefixWord ++ tailWord_362773) baseStart_362773 baseEnd_362773 := by
    simpa [prefixWord, tailWord_362773, baseEnd_362773] using wordTrace_append hprefix tailTrace_362773
  have hstable : (prefixWord ++ tailWord_362773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362773).length < 2 ^ (prefixWord ++ tailWord_362773).sum := by decide
  have hdescent : baseEnd_362773 < baseStart_362773 := by decide
  rcases family_descends (prefixWord ++ tailWord_362773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362832 : List Nat := [2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_362832 : Nat := 118140960795 + 362832 * 2 ^ 59
def prefixEnd_362832 : Nat := 4983230072969 + 3 ^ 40 * 362832 * 2
def baseEnd_362832 : Nat := 110404274270950904788961

theorem tailTrace_362832 : CollatzResearch.WordTrace tailWord_362832 prefixEnd_362832 110404274270950904788961 := by
  unfold tailWord_362832
  simp only [CollatzResearch.WordTrace]
  refine ⟨6616785110764552808641375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8822380147686070411521833 6616785110764552808641375)
  ·
    refine ⟨9925177666146829212962063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6616785110764552808641375 9925177666146829212962063)
    ·
      refine ⟨14887766499220243819443095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9925177666146829212962063 14887766499220243819443095)
      ·
        refine ⟨22331649748830365729164643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14887766499220243819443095 22331649748830365729164643)
        ·
          refine ⟨33497474623245548593746965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22331649748830365729164643 33497474623245548593746965)
          ·
            refine ⟨1570194122964635090331889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33497474623245548593746965 1570194122964635090331889)
            ·
              refine ⟨1177645592223476317748917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1570194122964635090331889 1177645592223476317748917)
              ·
                refine ⟨110404274270950904788961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1177645592223476317748917 110404274270950904788961)
                ·
                  rfl

theorem cell19_362832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_362832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362832 prefixEnd_362832 := by exact prefixLift 362832
  have htrace : WordTrace (prefixWord ++ tailWord_362832) baseStart_362832 baseEnd_362832 := by
    simpa [prefixWord, tailWord_362832, baseEnd_362832] using wordTrace_append hprefix tailTrace_362832
  have hstable : (prefixWord ++ tailWord_362832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362832).length < 2 ^ (prefixWord ++ tailWord_362832).sum := by decide
  have hdescent : baseEnd_362832 < baseStart_362832 := by decide
  rcases family_descends (prefixWord ++ tailWord_362832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362887 : List Nat := [1, 1, 4, 2, 2, 1, 5, 3]
def baseStart_362887 : Nat := 118140960795 + 362887 * 2 ^ 59
def prefixEnd_362887 : Nat := 4983230072969 + 3 ^ 40 * 362887 * 2
def baseEnd_362887 : Nat := 110421009936727073566589

theorem tailTrace_362887 : CollatzResearch.WordTrace tailWord_362887 prefixEnd_362887 110421009936727073566589 := by
  unfold tailWord_362887
  simp only [CollatzResearch.WordTrace]
  refine ⟨13235576236329850010534915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8823717490886566673689943 13235576236329850010534915)
  ·
    refine ⟨19853364354494775015802373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13235576236329850010534915 19853364354494775015802373)
    ·
      refine ⟨3722505816467770315462945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19853364354494775015802373 3722505816467770315462945)
      ·
        refine ⟨2791879362350827736597209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3722505816467770315462945 2791879362350827736597209)
        ·
          refine ⟨2093909521763120802447907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2791879362350827736597209 2093909521763120802447907)
          ·
            refine ⟨3140864282644681203671861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093909521763120802447907 3140864282644681203671861)
            ·
              refine ⟨294456026497938862844237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3140864282644681203671861 294456026497938862844237)
              ·
                refine ⟨110421009936727073566589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294456026497938862844237 110421009936727073566589)
                ·
                  rfl

theorem cell19_362887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_362887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362887 prefixEnd_362887 := by exact prefixLift 362887
  have htrace : WordTrace (prefixWord ++ tailWord_362887) baseStart_362887 baseEnd_362887 := by
    simpa [prefixWord, tailWord_362887, baseEnd_362887] using wordTrace_append hprefix tailTrace_362887
  have hstable : (prefixWord ++ tailWord_362887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362887).length < 2 ^ (prefixWord ++ tailWord_362887).sum := by decide
  have hdescent : baseEnd_362887 < baseStart_362887 := by decide
  rcases family_descends (prefixWord ++ tailWord_362887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362965 : List Nat := [1, 3, 2, 3, 1, 2, 7]
def baseStart_362965 : Nat := 118140960795 + 362965 * 2 ^ 59
def prefixEnd_362965 : Nat := 4983230072969 + 3 ^ 40 * 362965 * 2
def baseEnd_362965 : Nat := 36814914717882001277681

theorem tailTrace_362965 : CollatzResearch.WordTrace tailWord_362965 prefixEnd_362965 36814914717882001277681 := by
  unfold tailWord_362965
  simp only [CollatzResearch.WordTrace]
  refine ⟨13238421130047269331874349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8825614086698179554582899 13238421130047269331874349)
  ·
    refine ⟨4964407923767725999452881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13238421130047269331874349 4964407923767725999452881)
    ·
      refine ⟨3723305942825794499589661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4964407923767725999452881 3723305942825794499589661)
      ·
        refine ⟨1396239728559672937346123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3723305942825794499589661 1396239728559672937346123)
        ·
          refine ⟨2094359592839509406019185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396239728559672937346123 2094359592839509406019185)
          ·
            refine ⟨1570769694629632054514389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094359592839509406019185 1570769694629632054514389)
            ·
              refine ⟨36814914717882001277681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1570769694629632054514389 36814914717882001277681)
              ·
                rfl

theorem cell19_362965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_362965 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362965 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362965 prefixEnd_362965 := by exact prefixLift 362965
  have htrace : WordTrace (prefixWord ++ tailWord_362965) baseStart_362965 baseEnd_362965 := by
    simpa [prefixWord, tailWord_362965, baseEnd_362965] using wordTrace_append hprefix tailTrace_362965
  have hstable : (prefixWord ++ tailWord_362965).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362965).length < 2 ^ (prefixWord ++ tailWord_362965).sum := by decide
  have hdescent : baseEnd_362965 < baseStart_362965 := by decide
  rcases family_descends (prefixWord ++ tailWord_362965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362978 : List Nat := [3, 3, 3, 2, 1, 1, 2, 4]
def baseStart_362978 : Nat := 118140960795 + 362978 * 2 ^ 59
def prefixEnd_362978 : Nat := 4983230072969 + 3 ^ 40 * 362978 * 2
def baseEnd_362978 : Nat := 110448699856465825544119

theorem tailTrace_362978 : CollatzResearch.WordTrace tailWord_362978 prefixEnd_362978 110448699856465825544119 := by
  unfold tailWord_362978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3309723819750043138024397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8825930186000115034731725 3309723819750043138024397)
  ·
    refine ⟨1241146432406266176759149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3309723819750043138024397 1241146432406266176759149)
    ·
      refine ⟨465429912152349816284681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1241146432406266176759149 465429912152349816284681)
      ·
        refine ⟨349072434114262362213511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465429912152349816284681 349072434114262362213511)
        ·
          refine ⟨523608651171393543320267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349072434114262362213511 523608651171393543320267)
          ·
            refine ⟨785412976757090314980401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523608651171393543320267 785412976757090314980401)
            ·
              refine ⟨589059732567817736235301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785412976757090314980401 589059732567817736235301)
              ·
                refine ⟨110448699856465825544119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 589059732567817736235301 110448699856465825544119)
                ·
                  rfl

theorem cell19_362978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_362978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362978 prefixEnd_362978 := by exact prefixLift 362978
  have htrace : WordTrace (prefixWord ++ tailWord_362978) baseStart_362978 baseEnd_362978 := by
    simpa [prefixWord, tailWord_362978, baseEnd_362978] using wordTrace_append hprefix tailTrace_362978
  have hstable : (prefixWord ++ tailWord_362978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362978).length < 2 ^ (prefixWord ++ tailWord_362978).sum := by decide
  have hdescent : baseEnd_362978 < baseStart_362978 := by decide
  rcases family_descends (prefixWord ++ tailWord_362978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362984 : List Nat := [2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_362984 : Nat := 118140960795 + 362984 * 2 ^ 59
def prefixEnd_362984 : Nat := 4983230072969 + 3 ^ 40 * 362984 * 2
def baseEnd_362984 : Nat := 110450525565459589410769

theorem tailTrace_362984 : CollatzResearch.WordTrace tailWord_362984 prefixEnd_362984 110450525565459589410769 := by
  unfold tailWord_362984
  simp only [CollatzResearch.WordTrace]
  refine ⟨6619557058489217788408003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8826076077985623717877337 6619557058489217788408003)
  ·
    refine ⟨9929335587733826682612005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6619557058489217788408003 9929335587733826682612005)
    ·
      refine ⟨1861750422700092502989751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9929335587733826682612005 1861750422700092502989751)
      ·
        refine ⟨2792625634050138754484627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861750422700092502989751 2792625634050138754484627)
        ·
          refine ⟨4188938451075208131726941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2792625634050138754484627 4188938451075208131726941)
          ·
            refine ⟨1570851919153203049397603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4188938451075208131726941 1570851919153203049397603)
            ·
              refine ⟨2356277878729804574096405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570851919153203049397603 2356277878729804574096405)
              ·
                refine ⟨110450525565459589410769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2356277878729804574096405 110450525565459589410769)
                ·
                  rfl

theorem cell19_362984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_362984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_362984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_362984 prefixEnd_362984 := by exact prefixLift 362984
  have htrace : WordTrace (prefixWord ++ tailWord_362984) baseStart_362984 baseEnd_362984 := by
    simpa [prefixWord, tailWord_362984, baseEnd_362984] using wordTrace_append hprefix tailTrace_362984
  have hstable : (prefixWord ++ tailWord_362984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362984).length < 2 ^ (prefixWord ++ tailWord_362984).sum := by decide
  have hdescent : baseEnd_362984 < baseStart_362984 := by decide
  rcases family_descends (prefixWord ++ tailWord_362984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363022 : List Nat := [4, 1, 1, 2, 3, 8]
def baseStart_363022 : Nat := 118140960795 + 363022 * 2 ^ 59
def prefixEnd_363022 : Nat := 4983230072969 + 3 ^ 40 * 363022 * 2
def baseEnd_363022 : Nat := 12273565376565195618469

theorem tailTrace_363022 : CollatzResearch.WordTrace tailWord_363022 prefixEnd_363022 12273565376565195618469 := by
  unfold tailWord_363022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1655062511355096008337415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8827000060560512044466213 1655062511355096008337415)
  ·
    refine ⟨2482593767032644012506123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1655062511355096008337415 2482593767032644012506123)
    ·
      refine ⟨3723890650548966018759185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2482593767032644012506123 3723890650548966018759185)
      ·
        refine ⟨2792917987911724514069389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3723890650548966018759185 2792917987911724514069389)
        ·
          refine ⟨1047344245466896692776021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2792917987911724514069389 1047344245466896692776021)
          ·
            refine ⟨12273565376565195618469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1047344245466896692776021 12273565376565195618469)
            ·
              rfl

theorem cell19_363022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 8].length) (baseStart_363022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363022 prefixEnd_363022 := by exact prefixLift 363022
  have htrace : WordTrace (prefixWord ++ tailWord_363022) baseStart_363022 baseEnd_363022 := by
    simpa [prefixWord, tailWord_363022, baseEnd_363022] using wordTrace_append hprefix tailTrace_363022
  have hstable : (prefixWord ++ tailWord_363022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363022).length < 2 ^ (prefixWord ++ tailWord_363022).sum := by decide
  have hdescent : baseEnd_363022 < baseStart_363022 := by decide
  rcases family_descends (prefixWord ++ tailWord_363022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363079 : List Nat := [1, 1, 4, 1, 4, 2, 6]
def baseStart_363079 : Nat := 118140960795 + 363079 * 2 ^ 59
def prefixEnd_363079 : Nat := 4983230072969 + 3 ^ 40 * 363079 * 2
def baseEnd_363079 : Nat := 36826477541509172433133

theorem tailTrace_363079 : CollatzResearch.WordTrace tailWord_363079 prefixEnd_363079 36826477541509172433133 := by
  unfold tailWord_363079
  simp only [CollatzResearch.WordTrace]
  refine ⟨13242579051634266801524291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8828386034422844534349527 13242579051634266801524291)
  ·
    refine ⟨19863868577451400202286437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13242579051634266801524291 19863868577451400202286437)
    ·
      refine ⟨3724475358272137537928707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19863868577451400202286437 3724475358272137537928707)
      ·
        refine ⟨5586713037408206306893061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3724475358272137537928707 5586713037408206306893061)
        ·
          refine ⟨1047508694514038682542449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5586713037408206306893061 1047508694514038682542449)
          ·
            refine ⟨785631520885529011906837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047508694514038682542449 785631520885529011906837)
            ·
              refine ⟨36826477541509172433133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 785631520885529011906837 36826477541509172433133)
              ·
                rfl

theorem cell19_363079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_363079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363079 prefixEnd_363079 := by exact prefixLift 363079
  have htrace : WordTrace (prefixWord ++ tailWord_363079) baseStart_363079 baseEnd_363079 := by
    simpa [prefixWord, tailWord_363079, baseEnd_363079] using wordTrace_append hprefix tailTrace_363079
  have hstable : (prefixWord ++ tailWord_363079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363079).length < 2 ^ (prefixWord ++ tailWord_363079).sum := by decide
  have hdescent : baseEnd_363079 < baseStart_363079 := by decide
  rcases family_descends (prefixWord ++ tailWord_363079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363136 : List Nat := [2, 1, 1, 2, 1, 7, 5]
def baseStart_363136 : Nat := 118140960795 + 363136 * 2 ^ 59
def prefixEnd_363136 : Nat := 4983230072969 + 3 ^ 40 * 363136 * 2
def baseEnd_363136 : Nat := 36832258953322758010859

theorem tailTrace_363136 : CollatzResearch.WordTrace tailWord_363136 prefixEnd_363136 36832258953322758010859 := by
  unfold tailWord_363136
  simp only [CollatzResearch.WordTrace]
  refine ⟨6622329006213882768174631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8829772008285177024232841 6622329006213882768174631)
  ·
    refine ⟨9933493509320824152261947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6622329006213882768174631 9933493509320824152261947)
    ·
      refine ⟨14900240263981236228392921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9933493509320824152261947 14900240263981236228392921)
      ·
        refine ⟨11175180197985927171294691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14900240263981236228392921 11175180197985927171294691)
        ·
          refine ⟨16762770296978890756942037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11175180197985927171294691 16762770296978890756942037)
          ·
            refine ⟨392877428835442752115829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16762770296978890756942037 392877428835442752115829)
            ·
              refine ⟨36832258953322758010859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 392877428835442752115829 36832258953322758010859)
              ·
                rfl

theorem cell19_363136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_363136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363136 prefixEnd_363136 := by exact prefixLift 363136
  have htrace : WordTrace (prefixWord ++ tailWord_363136) baseStart_363136 baseEnd_363136 := by
    simpa [prefixWord, tailWord_363136, baseEnd_363136] using wordTrace_append hprefix tailTrace_363136
  have hstable : (prefixWord ++ tailWord_363136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363136).length < 2 ^ (prefixWord ++ tailWord_363136).sum := by decide
  have hdescent : baseEnd_363136 < baseStart_363136 := by decide
  rcases family_descends (prefixWord ++ tailWord_363136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363210 : List Nat := [3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_363210 : Nat := 118140960795 + 363210 * 2 ^ 59
def prefixEnd_363210 : Nat := 4983230072969 + 3 ^ 40 * 363210 * 2
def baseEnd_363210 : Nat := 110519293937558028387931

theorem tailTrace_363210 : CollatzResearch.WordTrace tailWord_363210 prefixEnd_363210 110519293937558028387931 := by
  unfold tailWord_363210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311839253539919043635771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8831571342773117449695389 3311839253539919043635771)
  ·
    refine ⟨4967758880309878565453657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3311839253539919043635771 4967758880309878565453657)
    ·
      refine ⟨3725819160232408924090243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4967758880309878565453657 3725819160232408924090243)
      ·
        refine ⟨5588728740348613386135365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725819160232408924090243 5588728740348613386135365)
        ·
          refine ⟨1047886638815365009900381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5588728740348613386135365 1047886638815365009900381)
          ·
            refine ⟨392957489555761878712643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1047886638815365009900381 392957489555761878712643)
            ·
              refine ⟨589436234333642818068965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392957489555761878712643 589436234333642818068965)
              ·
                refine ⟨110519293937558028387931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 589436234333642818068965 110519293937558028387931)
                ·
                  rfl

theorem cell19_363210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_363210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363210 prefixEnd_363210 := by exact prefixLift 363210
  have htrace : WordTrace (prefixWord ++ tailWord_363210) baseStart_363210 baseEnd_363210 := by
    simpa [prefixWord, tailWord_363210, baseEnd_363210] using wordTrace_append hprefix tailTrace_363210
  have hstable : (prefixWord ++ tailWord_363210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363210).length < 2 ^ (prefixWord ++ tailWord_363210).sum := by decide
  have hdescent : baseEnd_363210 < baseStart_363210 := by decide
  rcases family_descends (prefixWord ++ tailWord_363210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363250 : List Nat := [3, 2, 1, 3, 1, 3, 6]
def baseStart_363250 : Nat := 118140960795 + 363250 * 2 ^ 59
def prefixEnd_363250 : Nat := 4983230072969 + 3 ^ 40 * 363250 * 2
def baseEnd_363250 : Nat := 36843821776949929166311

theorem tailTrace_363250 : CollatzResearch.WordTrace tailWord_363250 prefixEnd_363250 36843821776949929166311 := by
  unfold tailWord_363250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3312203983503690751499801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8832543956009842003999469 3312203983503690751499801)
  ·
    refine ⟨2484152987627768063624851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3312203983503690751499801 2484152987627768063624851)
    ·
      refine ⟨3726229481441652095437277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2484152987627768063624851 3726229481441652095437277)
      ·
        refine ⟨1397336055540619535788979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3726229481441652095437277 1397336055540619535788979)
        ·
          refine ⟨2096004083310929303683469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397336055540619535788979 2096004083310929303683469)
          ·
            refine ⟨786001531241598488881301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2096004083310929303683469 786001531241598488881301)
            ·
              refine ⟨36843821776949929166311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 786001531241598488881301 36843821776949929166311)
              ·
                rfl

theorem cell19_363250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_363250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363250 prefixEnd_363250 := by exact prefixLift 363250
  have htrace : WordTrace (prefixWord ++ tailWord_363250) baseStart_363250 baseEnd_363250 := by
    simpa [prefixWord, tailWord_363250, baseEnd_363250] using wordTrace_append hprefix tailTrace_363250
  have hstable : (prefixWord ++ tailWord_363250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363250).length < 2 ^ (prefixWord ++ tailWord_363250).sum := by decide
  have hdescent : baseEnd_363250 < baseStart_363250 := by decide
  rcases family_descends (prefixWord ++ tailWord_363250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363282 : List Nat := [3, 2, 4, 1, 2, 2, 2, 3]
def baseStart_363282 : Nat := 118140960795 + 363282 * 2 ^ 59
def prefixEnd_363282 : Nat := 4983230072969 + 3 ^ 40 * 363282 * 2
def baseEnd_363282 : Nat := 110541202445483194787735

theorem tailTrace_363282 : CollatzResearch.WordTrace tailWord_363282 prefixEnd_363282 110541202445483194787735 := by
  unfold tailWord_363282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3312495767474708117791025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8833322046599221647442733 3312495767474708117791025)
  ·
    refine ⟨2484371825606031088343269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3312495767474708117791025 2484371825606031088343269)
    ·
      refine ⟨465819717301130829064363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2484371825606031088343269 465819717301130829064363)
      ·
        refine ⟨698729575951696243596545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465819717301130829064363 698729575951696243596545)
        ·
          refine ⟨524047181963772182697409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698729575951696243596545 524047181963772182697409)
          ·
            refine ⟨393035386472829137023057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524047181963772182697409 393035386472829137023057)
            ·
              refine ⟨294776539854621852767293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393035386472829137023057 294776539854621852767293)
              ·
                refine ⟨110541202445483194787735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294776539854621852767293 110541202445483194787735)
                ·
                  rfl

theorem cell19_363282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_363282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363282 prefixEnd_363282 := by exact prefixLift 363282
  have htrace : WordTrace (prefixWord ++ tailWord_363282) baseStart_363282 baseEnd_363282 := by
    simpa [prefixWord, tailWord_363282, baseEnd_363282] using wordTrace_append hprefix tailTrace_363282
  have hstable : (prefixWord ++ tailWord_363282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363282).length < 2 ^ (prefixWord ++ tailWord_363282).sum := by decide
  have hdescent : baseEnd_363282 < baseStart_363282 := by decide
  rcases family_descends (prefixWord ++ tailWord_363282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363362 : List Nat := [3, 3, 2, 1, 4, 6]
def baseStart_363362 : Nat := 118140960795 + 363362 * 2 ^ 59
def prefixEnd_363362 : Nat := 4983230072969 + 3 ^ 40 * 363362 * 2
def baseEnd_363362 : Nat := 12285060581340745889971

theorem tailTrace_363362 : CollatzResearch.WordTrace tailWord_363362 prefixEnd_363362 12285060581340745889971 := by
  unfold tailWord_363362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3313225227402251533519085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8835267273072670756050893 3313225227402251533519085)
  ·
    refine ⟨1242459460275844325069657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3313225227402251533519085 1242459460275844325069657)
    ·
      refine ⟨931844595206883243802243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1242459460275844325069657 931844595206883243802243)
      ·
        refine ⟨1397766892810324865703365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931844595206883243802243 1397766892810324865703365)
        ·
          refine ⟨262081292401935912319381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1397766892810324865703365 262081292401935912319381)
          ·
            refine ⟨12285060581340745889971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262081292401935912319381 12285060581340745889971)
            ·
              rfl

theorem cell19_363362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 6].length) (baseStart_363362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363362 prefixEnd_363362 := by exact prefixLift 363362
  have htrace : WordTrace (prefixWord ++ tailWord_363362) baseStart_363362 baseEnd_363362 := by
    simpa [prefixWord, tailWord_363362, baseEnd_363362] using wordTrace_append hprefix tailTrace_363362
  have hstable : (prefixWord ++ tailWord_363362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363362).length < 2 ^ (prefixWord ++ tailWord_363362).sum := by decide
  have hdescent : baseEnd_363362 < baseStart_363362 := by decide
  rcases family_descends (prefixWord ++ tailWord_363362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363381 : List Nat := [1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_363381 : Nat := 118140960795 + 363381 * 2 ^ 59
def prefixEnd_363381 : Nat := 4983230072969 + 3 ^ 40 * 363381 * 2
def baseEnd_363381 : Nat := 110571326643880298587465

theorem tailTrace_363381 : CollatzResearch.WordTrace tailWord_363381 prefixEnd_363381 110571326643880298587465 := by
  unfold tailWord_363381
  simp only [CollatzResearch.WordTrace]
  refine ⟨13253593896540172379017997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8835729264360114919345331 13253593896540172379017997)
  ·
    refine ⟨4970097711202564642131749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13253593896540172379017997 4970097711202564642131749)
    ·
      refine ⟨931893320850480870399703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4970097711202564642131749 931893320850480870399703)
      ·
        refine ⟨1397839981275721305599555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931893320850480870399703 1397839981275721305599555)
        ·
          refine ⟨2096759971913581958399333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397839981275721305599555 2096759971913581958399333)
          ·
            refine ⟨393142494733796617199875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2096759971913581958399333 393142494733796617199875)
            ·
              refine ⟨589713742100694925799813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393142494733796617199875 589713742100694925799813)
              ·
                refine ⟨110571326643880298587465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 589713742100694925799813 110571326643880298587465)
                ·
                  rfl

theorem cell19_363381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_363381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363381 prefixEnd_363381 := by exact prefixLift 363381
  have htrace : WordTrace (prefixWord ++ tailWord_363381) baseStart_363381 baseEnd_363381 := by
    simpa [prefixWord, tailWord_363381, baseEnd_363381] using wordTrace_append hprefix tailTrace_363381
  have hstable : (prefixWord ++ tailWord_363381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363381).length < 2 ^ (prefixWord ++ tailWord_363381).sum := by decide
  have hdescent : baseEnd_363381 < baseStart_363381 := by decide
  rcases family_descends (prefixWord ++ tailWord_363381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363400 : List Nat := [2, 1, 3, 3, 2, 2, 3, 3]
def baseStart_363400 : Nat := 118140960795 + 363400 * 2 ^ 59
def prefixEnd_363400 : Nat := 4983230072969 + 3 ^ 40 * 363400 * 2
def baseEnd_363400 : Nat := 110577108055693884165191

theorem tailTrace_363400 : CollatzResearch.WordTrace tailWord_363400 prefixEnd_363400 110577108055693884165191 := by
  unfold tailWord_363400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6627143441735669311979827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8836191255647559082639769 6627143441735669311979827)
  ·
    refine ⟨9940715162603503967969741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6627143441735669311979827 9940715162603503967969741)
    ·
      refine ⟨3727768185976313987988653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9940715162603503967969741 3727768185976313987988653)
      ·
        refine ⟨1397913069741117745495745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3727768185976313987988653 1397913069741117745495745)
        ·
          refine ⟨1048434802305838309121809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1397913069741117745495745 1048434802305838309121809)
          ·
            refine ⟨786326101729378731841357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048434802305838309121809 786326101729378731841357)
            ·
              refine ⟨294872288148517024440509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 786326101729378731841357 294872288148517024440509)
              ·
                refine ⟨110577108055693884165191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294872288148517024440509 110577108055693884165191)
                ·
                  rfl

theorem cell19_363400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_363400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363400 prefixEnd_363400 := by exact prefixLift 363400
  have htrace : WordTrace (prefixWord ++ tailWord_363400) baseStart_363400 baseEnd_363400 := by
    simpa [prefixWord, tailWord_363400, baseEnd_363400] using wordTrace_append hprefix tailTrace_363400
  have hstable : (prefixWord ++ tailWord_363400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363400).length < 2 ^ (prefixWord ++ tailWord_363400).sum := by decide
  have hdescent : baseEnd_363400 < baseStart_363400 := by decide
  rcases family_descends (prefixWord ++ tailWord_363400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363404 : List Nat := [2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_363404 : Nat := 118140960795 + 363404 * 2 ^ 59
def prefixEnd_363404 : Nat := 4983230072969 + 3 ^ 40 * 363404 * 2
def baseEnd_363404 : Nat := 110578325195023060076291

theorem tailTrace_363404 : CollatzResearch.WordTrace tailWord_363404 prefixEnd_363404 110578325195023060076291 := by
  unfold tailWord_363404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6627216387728423653552633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8836288516971231538070177 6627216387728423653552633)
  ·
    refine ⟨4970412290796317740164475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6627216387728423653552633 4970412290796317740164475)
    ·
      refine ⟨7455618436194476610246713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4970412290796317740164475 7455618436194476610246713)
      ·
        refine ⟨5591713827145857457685035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7455618436194476610246713 5591713827145857457685035)
        ·
          refine ⟨8387570740718786186527553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591713827145857457685035 8387570740718786186527553)
          ·
            refine ⟨6290678055539089639895665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8387570740718786186527553 6290678055539089639895665)
            ·
              refine ⟨4718008541654317229921749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6290678055539089639895665 4718008541654317229921749)
              ·
                refine ⟨110578325195023060076291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4718008541654317229921749 110578325195023060076291)
                ·
                  rfl

theorem cell19_363404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_363404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363404 prefixEnd_363404 := by exact prefixLift 363404
  have htrace : WordTrace (prefixWord ++ tailWord_363404) baseStart_363404 baseEnd_363404 := by
    simpa [prefixWord, tailWord_363404, baseEnd_363404] using wordTrace_append hprefix tailTrace_363404
  have hstable : (prefixWord ++ tailWord_363404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363404).length < 2 ^ (prefixWord ++ tailWord_363404).sum := by decide
  have hdescent : baseEnd_363404 < baseStart_363404 := by decide
  rcases family_descends (prefixWord ++ tailWord_363404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363480 : List Nat := [2, 1, 2, 2, 2, 3, 7]
def baseStart_363480 : Nat := 118140960795 + 363480 * 2 ^ 59
def prefixEnd_363480 : Nat := 4983230072969 + 3 ^ 40 * 363480 * 2
def baseEnd_363480 : Nat := 36867150280759134129065

theorem tailTrace_363480 : CollatzResearch.WordTrace tailWord_363480 prefixEnd_363480 36867150280759134129065 := by
  unfold tailWord_363480
  simp only [CollatzResearch.WordTrace]
  refine ⟨6628602361590756143435947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8838136482121008191247929 6628602361590756143435947)
  ·
    refine ⟨9942903542386134215153921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6628602361590756143435947 9942903542386134215153921)
    ·
      refine ⟨7457177656789600661365441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9942903542386134215153921 7457177656789600661365441)
      ·
        refine ⟨5592883242592200496024081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7457177656789600661365441 5592883242592200496024081)
        ·
          refine ⟨4194662431944150372018061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5592883242592200496024081 4194662431944150372018061)
          ·
            refine ⟨1572998411979056389506773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4194662431944150372018061 1572998411979056389506773)
            ·
              refine ⟨36867150280759134129065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1572998411979056389506773 36867150280759134129065)
              ·
                rfl

theorem cell19_363480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_363480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363480 prefixEnd_363480 := by exact prefixLift 363480
  have htrace : WordTrace (prefixWord ++ tailWord_363480) baseStart_363480 baseEnd_363480 := by
    simpa [prefixWord, tailWord_363480, baseEnd_363480] using wordTrace_append hprefix tailTrace_363480
  have hstable : (prefixWord ++ tailWord_363480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363480).length < 2 ^ (prefixWord ++ tailWord_363480).sum := by decide
  have hdescent : baseEnd_363480 < baseStart_363480 := by decide
  rcases family_descends (prefixWord ++ tailWord_363480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363554 : List Nat := [3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_363554 : Nat := 118140960795 + 363554 * 2 ^ 59
def prefixEnd_363554 : Nat := 4983230072969 + 3 ^ 40 * 363554 * 2
def baseEnd_363554 : Nat := 110623967919867156742549

theorem tailTrace_363554 : CollatzResearch.WordTrace tailWord_363554 prefixEnd_363554 110623967919867156742549 := by
  unfold tailWord_363554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314975931228355731266429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8839935816608948616710477 3314975931228355731266429)
  ·
    refine ⟨1243115974210633399224911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3314975931228355731266429 1243115974210633399224911)
    ·
      refine ⟨1864673961315950098837367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243115974210633399224911 1864673961315950098837367)
      ·
        refine ⟨2797010941973925148256051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864673961315950098837367 2797010941973925148256051)
        ·
          refine ⟨4195516412960887722384077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797010941973925148256051 4195516412960887722384077)
          ·
            refine ⟨1573318654860332895894029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4195516412960887722384077 1573318654860332895894029)
            ·
              refine ⟨589994495572624835960261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1573318654860332895894029 589994495572624835960261)
              ·
                refine ⟨110623967919867156742549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 589994495572624835960261 110623967919867156742549)
                ·
                  rfl

theorem cell19_363554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_363554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363554 prefixEnd_363554 := by exact prefixLift 363554
  have htrace : WordTrace (prefixWord ++ tailWord_363554) baseStart_363554 baseEnd_363554 := by
    simpa [prefixWord, tailWord_363554, baseEnd_363554] using wordTrace_append hprefix tailTrace_363554
  have hstable : (prefixWord ++ tailWord_363554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363554).length < 2 ^ (prefixWord ++ tailWord_363554).sum := by decide
  have hdescent : baseEnd_363554 < baseStart_363554 := by decide
  rcases family_descends (prefixWord ++ tailWord_363554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363590 : List Nat := [6, 1, 1, 1, 1, 3, 6]
def baseStart_363590 : Nat := 118140960795 + 363590 * 2 ^ 59
def prefixEnd_363590 : Nat := 4983230072969 + 3 ^ 40 * 363590 * 2
def baseEnd_363590 : Nat := 36878307391276579980817

theorem tailTrace_363590 : CollatzResearch.WordTrace tailWord_363590 prefixEnd_363590 36878307391276579980817 := by
  unfold tailWord_363590
  simp only [CollatzResearch.WordTrace]
  refine ⟨414413023524468783543007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8840811168522000715584149 414413023524468783543007)
  ·
    refine ⟨621619535286703175314511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414413023524468783543007 621619535286703175314511)
    ·
      refine ⟨932429302930054762971767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621619535286703175314511 932429302930054762971767)
      ·
        refine ⟨1398643954395082144457651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932429302930054762971767 1398643954395082144457651)
        ·
          refine ⟨2097965931592623216686477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398643954395082144457651 2097965931592623216686477)
          ·
            refine ⟨786737224347233706257429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2097965931592623216686477 786737224347233706257429)
            ·
              refine ⟨36878307391276579980817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 786737224347233706257429 36878307391276579980817)
              ·
                rfl

theorem cell19_363590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_363590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363590 prefixEnd_363590 := by exact prefixLift 363590
  have htrace : WordTrace (prefixWord ++ tailWord_363590) baseStart_363590 baseEnd_363590 := by
    simpa [prefixWord, tailWord_363590, baseEnd_363590] using wordTrace_append hprefix tailTrace_363590
  have hstable : (prefixWord ++ tailWord_363590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363590).length < 2 ^ (prefixWord ++ tailWord_363590).sum := by decide
  have hdescent : baseEnd_363590 < baseStart_363590 := by decide
  rcases family_descends (prefixWord ++ tailWord_363590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363624 : List Nat := [2, 1, 4, 4, 2, 1, 2, 3]
def baseStart_363624 : Nat := 118140960795 + 363624 * 2 ^ 59
def prefixEnd_363624 : Nat := 4983230072969 + 3 ^ 40 * 363624 * 2
def baseEnd_363624 : Nat := 110645267858127735186803

theorem tailTrace_363624 : CollatzResearch.WordTrace tailWord_363624 prefixEnd_363624 110645267858127735186803 := by
  unfold tailWord_363624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631228417329912440056963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8841637889773216586742617 6631228417329912440056963)
  ·
    refine ⟨9946842625994868660085445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6631228417329912440056963 9946842625994868660085445)
    ·
      refine ⟨1865032992374037873766021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9946842625994868660085445 1865032992374037873766021)
      ·
        refine ⟨349693686070132101331129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1865032992374037873766021 349693686070132101331129)
        ·
          refine ⟨262270264552599075998347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349693686070132101331129 262270264552599075998347)
          ·
            refine ⟨393405396828898613997521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262270264552599075998347 393405396828898613997521)
            ·
              refine ⟨295054047621673960498141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393405396828898613997521 295054047621673960498141)
              ·
                refine ⟨110645267858127735186803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295054047621673960498141 110645267858127735186803)
                ·
                  rfl

theorem cell19_363624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_363624 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363624 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363624 prefixEnd_363624 := by exact prefixLift 363624
  have htrace : WordTrace (prefixWord ++ tailWord_363624) baseStart_363624 baseEnd_363624 := by
    simpa [prefixWord, tailWord_363624, baseEnd_363624] using wordTrace_append hprefix tailTrace_363624
  have hstable : (prefixWord ++ tailWord_363624).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363624).length < 2 ^ (prefixWord ++ tailWord_363624).sum := by decide
  have hdescent : baseEnd_363624 < baseStart_363624 := by decide
  rcases family_descends (prefixWord ++ tailWord_363624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363630 : List Nat := [4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_363630 : Nat := 118140960795 + 363630 * 2 ^ 59
def prefixEnd_363630 : Nat := 4983230072969 + 3 ^ 40 * 363630 * 2
def baseEnd_363630 : Nat := 110647093567121499053453

theorem tailTrace_363630 : CollatzResearch.WordTrace tailWord_363630 prefixEnd_363630 110647093567121499053453 := by
  unfold tailWord_363630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657834459079760988104043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8841783781758725269888229 1657834459079760988104043)
  ·
    refine ⟨2486751688619641482156065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1657834459079760988104043 2486751688619641482156065)
    ·
      refine ⟨1865063766464731111617049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2486751688619641482156065 1865063766464731111617049)
      ·
        refine ⟨1398797824848548333712787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1865063766464731111617049 1398797824848548333712787)
        ·
          refine ⟨2098196737272822500569181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398797824848548333712787 2098196737272822500569181)
          ·
            refine ⟨786823776477308437713443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2098196737272822500569181 786823776477308437713443)
            ·
              refine ⟨1180235664715962656570165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786823776477308437713443 1180235664715962656570165)
              ·
                refine ⟨110647093567121499053453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1180235664715962656570165 110647093567121499053453)
                ·
                  rfl

theorem cell19_363630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_363630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363630 prefixEnd_363630 := by exact prefixLift 363630
  have htrace : WordTrace (prefixWord ++ tailWord_363630) baseStart_363630 baseEnd_363630 := by
    simpa [prefixWord, tailWord_363630, baseEnd_363630] using wordTrace_append hprefix tailTrace_363630
  have hstable : (prefixWord ++ tailWord_363630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363630).length < 2 ^ (prefixWord ++ tailWord_363630).sum := by decide
  have hdescent : baseEnd_363630 < baseStart_363630 := by decide
  rcases family_descends (prefixWord ++ tailWord_363630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363632 : List Nat := [2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_363632 : Nat := 118140960795 + 363632 * 2 ^ 59
def prefixEnd_363632 : Nat := 4983230072969 + 3 ^ 40 * 363632 * 2
def baseEnd_363632 : Nat := 110647702136786087009003

theorem tailTrace_363632 : CollatzResearch.WordTrace tailWord_363632 prefixEnd_363632 110647702136786087009003 := by
  unfold tailWord_363632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631374309315421123202575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8841832412420561497603433 6631374309315421123202575)
  ·
    refine ⟨9947061463973131684803863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6631374309315421123202575 9947061463973131684803863)
    ·
      refine ⟨14920592195959697527205795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9947061463973131684803863 14920592195959697527205795)
      ·
        refine ⟨22380888293939546290808693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14920592195959697527205795 22380888293939546290808693)
        ·
          refine ⟨2098208277556832464763315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22380888293939546290808693 2098208277556832464763315)
          ·
            refine ⟨3147312416335248697144973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098208277556832464763315 3147312416335248697144973)
            ·
              refine ⟨1180242156125718261429365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3147312416335248697144973 1180242156125718261429365)
              ·
                refine ⟨110647702136786087009003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1180242156125718261429365 110647702136786087009003)
                ·
                  rfl

theorem cell19_363632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_363632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363632 prefixEnd_363632 := by exact prefixLift 363632
  have htrace : WordTrace (prefixWord ++ tailWord_363632) baseStart_363632 baseEnd_363632 := by
    simpa [prefixWord, tailWord_363632, baseEnd_363632] using wordTrace_append hprefix tailTrace_363632
  have hstable : (prefixWord ++ tailWord_363632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363632).length < 2 ^ (prefixWord ++ tailWord_363632).sum := by decide
  have hdescent : baseEnd_363632 < baseStart_363632 := by decide
  rcases family_descends (prefixWord ++ tailWord_363632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363649 : List Nat := [1, 2, 4, 2, 2, 3, 5]
def baseStart_363649 : Nat := 118140960795 + 363649 * 2 ^ 59
def prefixEnd_363649 : Nat := 4983230072969 + 3 ^ 40 * 363649 * 2
def baseEnd_363649 : Nat := 36884291659645028210393

theorem tailTrace_363649 : CollatzResearch.WordTrace tailWord_363649 prefixEnd_363649 36884291659645028210393 := by
  unfold tailWord_363649
  simp only [CollatzResearch.WordTrace]
  refine ⟨13263368659569254149774001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8842245773046169433182667 13263368659569254149774001)
  ·
    refine ⟨9947526494676940612330501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13263368659569254149774001 9947526494676940612330501)
    ·
      refine ⟨1865161217751926364811969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9947526494676940612330501 1865161217751926364811969)
      ·
        refine ⟨1398870913313944773608977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1865161217751926364811969 1398870913313944773608977)
        ·
          refine ⟨1049153184985458580206733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1398870913313944773608977 1049153184985458580206733)
          ·
            refine ⟨393432444369546967577525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1049153184985458580206733 393432444369546967577525)
            ·
              refine ⟨36884291659645028210393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 393432444369546967577525 36884291659645028210393)
              ·
                rfl

theorem cell19_363649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_363649 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363649 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363649 prefixEnd_363649 := by exact prefixLift 363649
  have htrace : WordTrace (prefixWord ++ tailWord_363649) baseStart_363649 baseEnd_363649 := by
    simpa [prefixWord, tailWord_363649, baseEnd_363649] using wordTrace_append hprefix tailTrace_363649
  have hstable : (prefixWord ++ tailWord_363649).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363649).length < 2 ^ (prefixWord ++ tailWord_363649).sum := by decide
  have hdescent : baseEnd_363649 < baseStart_363649 := by decide
  rcases family_descends (prefixWord ++ tailWord_363649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363687 : List Nat := [1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_363687 : Nat := 118140960795 + 363687 * 2 ^ 59
def prefixEnd_363687 : Nat := 4983230072969 + 3 ^ 40 * 363687 * 2
def baseEnd_363687 : Nat := 110664437802562255786631

theorem tailTrace_363687 : CollatzResearch.WordTrace tailWord_363687 prefixEnd_363687 110664437802562255786631 := by
  unfold tailWord_363687
  simp only [CollatzResearch.WordTrace]
  refine ⟨13264754633431586639657315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8843169755621057759771543 13264754633431586639657315)
  ·
    refine ⟨19897131950147379959485973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13264754633431586639657315 19897131950147379959485973)
    ·
      refine ⟨932678060163158435600905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19897131950147379959485973 932678060163158435600905)
      ·
        refine ⟨699508545122368826700679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 932678060163158435600905 699508545122368826700679)
        ·
          refine ⟨1049262817683553240051019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699508545122368826700679 1049262817683553240051019)
          ·
            refine ⟨1573894226525329860076529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049262817683553240051019 1573894226525329860076529)
            ·
              refine ⟨1180420669893997395057397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1573894226525329860076529 1180420669893997395057397)
              ·
                refine ⟨110664437802562255786631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1180420669893997395057397 110664437802562255786631)
                ·
                  rfl

theorem cell19_363687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_363687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363687 prefixEnd_363687 := by exact prefixLift 363687
  have htrace : WordTrace (prefixWord ++ tailWord_363687) baseStart_363687 baseEnd_363687 := by
    simpa [prefixWord, tailWord_363687, baseEnd_363687] using wordTrace_append hprefix tailTrace_363687
  have hstable : (prefixWord ++ tailWord_363687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363687).length < 2 ^ (prefixWord ++ tailWord_363687).sum := by decide
  have hdescent : baseEnd_363687 < baseStart_363687 := by decide
  rcases family_descends (prefixWord ++ tailWord_363687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363702 : List Nat := [5, 1, 3, 2, 2, 6]
def baseStart_363702 : Nat := 118140960795 + 363702 * 2 ^ 59
def prefixEnd_363702 : Nat := 4983230072969 + 3 ^ 40 * 363702 * 2
def baseEnd_363702 : Nat := 12296555786116296161473

theorem tailTrace_363702 : CollatzResearch.WordTrace tailWord_363702 prefixEnd_363702 12296555786116296161473 := by
  unfold tailWord_363702
  simp only [CollatzResearch.WordTrace]
  refine ⟨829081358023577762590835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8843534485584829467635573 829081358023577762590835)
  ·
    refine ⟨1243622037035366643886253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829081358023577762590835 1243622037035366643886253)
    ·
      refine ⟨466358263888262491457345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1243622037035366643886253 466358263888262491457345)
      ·
        refine ⟨349768697916196868593009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466358263888262491457345 349768697916196868593009)
        ·
          refine ⟨262326523437147651444757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349768697916196868593009 262326523437147651444757)
          ·
            refine ⟨12296555786116296161473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262326523437147651444757 12296555786116296161473)
            ·
              rfl

theorem cell19_363702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 6].length) (baseStart_363702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363702 prefixEnd_363702 := by exact prefixLift 363702
  have htrace : WordTrace (prefixWord ++ tailWord_363702) baseStart_363702 baseEnd_363702 := by
    simpa [prefixWord, tailWord_363702, baseEnd_363702] using wordTrace_append hprefix tailTrace_363702
  have hstable : (prefixWord ++ tailWord_363702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363702).length < 2 ^ (prefixWord ++ tailWord_363702).sum := by decide
  have hdescent : baseEnd_363702 < baseStart_363702 := by decide
  rcases family_descends (prefixWord ++ tailWord_363702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363708 : List Nat := [2, 2, 2, 3, 2, 8]
def baseStart_363708 : Nat := 118140960795 + 363708 * 2 ^ 59
def prefixEnd_363708 : Nat := 4983230072969 + 3 ^ 40 * 363708 * 2
def baseEnd_363708 : Nat := 12296758642671158813323

theorem tailTrace_363708 : CollatzResearch.WordTrace tailWord_363708 prefixEnd_363708 12296758642671158813323 := by
  unfold tailWord_363708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6632760283177753613085889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8843680377570338150781185 6632760283177753613085889)
  ·
    refine ⟨4974570212383315209814417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6632760283177753613085889 4974570212383315209814417)
    ·
      refine ⟨3730927659287486407360813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4974570212383315209814417 3730927659287486407360813)
      ·
        refine ⟨1399097872232807402760305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3730927659287486407360813 1399097872232807402760305)
        ·
          refine ⟨1049323404174605552070229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1399097872232807402760305 1049323404174605552070229)
          ·
            refine ⟨12296758642671158813323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1049323404174605552070229 12296758642671158813323)
            ·
              rfl

theorem cell19_363708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 8].length) (baseStart_363708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363708 prefixEnd_363708 := by exact prefixLift 363708
  have htrace : WordTrace (prefixWord ++ tailWord_363708) baseStart_363708 baseEnd_363708 := by
    simpa [prefixWord, tailWord_363708, baseEnd_363708] using wordTrace_append hprefix tailTrace_363708
  have hstable : (prefixWord ++ tailWord_363708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363708).length < 2 ^ (prefixWord ++ tailWord_363708).sum := by decide
  have hdescent : baseEnd_363708 < baseStart_363708 := by decide
  rcases family_descends (prefixWord ++ tailWord_363708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363744 : List Nat := [2, 1, 1, 3, 1, 5, 3, 3]
def baseStart_363744 : Nat := 118140960795 + 363744 * 2 ^ 59
def prefixEnd_363744 : Nat := 4983230072969 + 3 ^ 40 * 363744 * 2
def baseEnd_363744 : Nat := 110681782038003012519809

theorem tailTrace_363744 : CollatzResearch.WordTrace tailWord_363744 prefixEnd_363744 110681782038003012519809 := by
  unfold tailWord_363744
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633416797112542687241143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8844555729483390249654857 6633416797112542687241143)
  ·
    refine ⟨9950125195668814030861715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6633416797112542687241143 9950125195668814030861715)
    ·
      refine ⟨14925187793503221046292573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9950125195668814030861715 14925187793503221046292573)
      ·
        refine ⟨5596945422563707892359715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14925187793503221046292573 5596945422563707892359715)
        ·
          refine ⟨8395418133845561838539573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5596945422563707892359715 8395418133845561838539573)
          ·
            refine ⟨787070450048021422363085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8395418133845561838539573 787070450048021422363085)
            ·
              refine ⟨295151418768008033386157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 787070450048021422363085 295151418768008033386157)
              ·
                refine ⟨110681782038003012519809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295151418768008033386157 110681782038003012519809)
                ·
                  rfl

theorem cell19_363744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_363744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363744 prefixEnd_363744 := by exact prefixLift 363744
  have htrace : WordTrace (prefixWord ++ tailWord_363744) baseStart_363744 baseEnd_363744 := by
    simpa [prefixWord, tailWord_363744, baseEnd_363744] using wordTrace_append hprefix tailTrace_363744
  have hstable : (prefixWord ++ tailWord_363744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363744).length < 2 ^ (prefixWord ++ tailWord_363744).sum := by decide
  have hdescent : baseEnd_363744 < baseStart_363744 := by decide
  rcases family_descends (prefixWord ++ tailWord_363744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363837 : List Nat := [1, 4, 1, 5, 1, 1, 2, 4]
def baseStart_363837 : Nat := 118140960795 + 363837 * 2 ^ 59
def prefixEnd_363837 : Nat := 4983230072969 + 3 ^ 40 * 363837 * 2
def baseEnd_363837 : Nat := 110710080527406352452889

theorem tailTrace_363837 : CollatzResearch.WordTrace tailWord_363837 prefixEnd_363837 110710080527406352452889 := by
  unfold tailWord_363837
  simp only [CollatzResearch.WordTrace]
  refine ⟨13270225582888162257617765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8846817055258774838411843 13270225582888162257617765)
  ·
    refine ⟨2488167296791530423303331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13270225582888162257617765 2488167296791530423303331)
    ·
      refine ⟨3732250945187295634954997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488167296791530423303331 3732250945187295634954997)
      ·
        refine ⟨349898526111308965777031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3732250945187295634954997 349898526111308965777031)
        ·
          refine ⟨524847789166963448665547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349898526111308965777031 524847789166963448665547)
          ·
            refine ⟨787271683750445172998321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524847789166963448665547 787271683750445172998321)
            ·
              refine ⟨590453762812833879748741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787271683750445172998321 590453762812833879748741)
              ·
                refine ⟨110710080527406352452889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590453762812833879748741 110710080527406352452889)
                ·
                  rfl

theorem cell19_363837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_363837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363837 prefixEnd_363837 := by exact prefixLift 363837
  have htrace : WordTrace (prefixWord ++ tailWord_363837) baseStart_363837 baseEnd_363837 := by
    simpa [prefixWord, tailWord_363837, baseEnd_363837] using wordTrace_append hprefix tailTrace_363837
  have hstable : (prefixWord ++ tailWord_363837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363837).length < 2 ^ (prefixWord ++ tailWord_363837).sum := by decide
  have hdescent : baseEnd_363837 < baseStart_363837 := by decide
  rcases family_descends (prefixWord ++ tailWord_363837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363860 : List Nat := [2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_363860 : Nat := 118140960795 + 363860 * 2 ^ 59
def prefixEnd_363860 : Nat := 4983230072969 + 3 ^ 40 * 363860 * 2
def baseEnd_363860 : Nat := 110717079078549113941715

theorem tailTrace_363860 : CollatzResearch.WordTrace tailWord_363860 prefixEnd_363860 110717079078549113941715 := by
  unfold tailWord_363860
  simp only [CollatzResearch.WordTrace]
  refine ⟨6635532230902418592852517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8847376307869891457136689 6635532230902418592852517)
  ·
    refine ⟨1244162293294203486159847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6635532230902418592852517 1244162293294203486159847)
    ·
      refine ⟨1866243439941305229239771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1244162293294203486159847 1866243439941305229239771)
      ·
        refine ⟨2799365159911957843859657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866243439941305229239771 2799365159911957843859657)
        ·
          refine ⟨2099523869933968382894743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2799365159911957843859657 2099523869933968382894743)
          ·
            refine ⟨3149285804900952574342115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099523869933968382894743 3149285804900952574342115)
            ·
              refine ⟨4723928707351428861513173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149285804900952574342115 4723928707351428861513173)
              ·
                refine ⟨110717079078549113941715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4723928707351428861513173 110717079078549113941715)
                ·
                  rfl

theorem cell19_363860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_363860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363860 prefixEnd_363860 := by exact prefixLift 363860
  have htrace : WordTrace (prefixWord ++ tailWord_363860) baseStart_363860 baseEnd_363860 := by
    simpa [prefixWord, tailWord_363860, baseEnd_363860] using wordTrace_append hprefix tailTrace_363860
  have hstable : (prefixWord ++ tailWord_363860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363860).length < 2 ^ (prefixWord ++ tailWord_363860).sum := by decide
  have hdescent : baseEnd_363860 < baseStart_363860 := by decide
  rcases family_descends (prefixWord ++ tailWord_363860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363879 : List Nat := [1, 1, 5, 1, 4, 7]
def baseStart_363879 : Nat := 118140960795 + 363879 * 2 ^ 59
def prefixEnd_363879 : Nat := 4983230072969 + 3 ^ 40 * 363879 * 2
def baseEnd_363879 : Nat := 12302540054484744391049

theorem tailTrace_363879 : CollatzResearch.WordTrace tailWord_363879 prefixEnd_363879 12302540054484744391049 := by
  unfold tailWord_363879
  simp only [CollatzResearch.WordTrace]
  refine ⟨13271757448736003430646691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8847838299157335620431127 13271757448736003430646691)
  ·
    refine ⟨19907636173104005145970037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13271757448736003430646691 19907636173104005145970037)
    ·
      refine ⟨1866340891228500482434691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19907636173104005145970037 1866340891228500482434691)
      ·
        refine ⟨2799511336842750723652037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866340891228500482434691 2799511336842750723652037)
        ·
          refine ⟨524908375658015760684757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2799511336842750723652037 524908375658015760684757)
          ·
            refine ⟨12302540054484744391049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 524908375658015760684757 12302540054484744391049)
            ·
              rfl

theorem cell19_363879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 7].length) (baseStart_363879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363879 prefixEnd_363879 := by exact prefixLift 363879
  have htrace : WordTrace (prefixWord ++ tailWord_363879) baseStart_363879 baseEnd_363879 := by
    simpa [prefixWord, tailWord_363879, baseEnd_363879] using wordTrace_append hprefix tailTrace_363879
  have hstable : (prefixWord ++ tailWord_363879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363879).length < 2 ^ (prefixWord ++ tailWord_363879).sum := by decide
  have hdescent : baseEnd_363879 < baseStart_363879 := by decide
  rcases family_descends (prefixWord ++ tailWord_363879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363972 : List Nat := [2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_363972 : Nat := 118140960795 + 363972 * 2 ^ 59
def prefixEnd_363972 : Nat := 4983230072969 + 3 ^ 40 * 363972 * 2
def baseEnd_363972 : Nat := 110751158979766039452521

theorem tailTrace_363972 : CollatzResearch.WordTrace tailWord_363972 prefixEnd_363972 110751158979766039452521 := by
  unfold tailWord_363972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6637574718699540156891085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8850099624932720209188113 6637574718699540156891085)
  ·
    refine ⟨2489090519512327558834157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6637574718699540156891085 2489090519512327558834157)
    ·
      refine ⟨933408944817122834562809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2489090519512327558834157 933408944817122834562809)
      ·
        refine ⟨700056708612842125922107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 933408944817122834562809 700056708612842125922107)
        ·
          refine ⟨1050085062919263188883161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700056708612842125922107 1050085062919263188883161)
          ·
            refine ⟨787563797189447391662371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050085062919263188883161 787563797189447391662371)
            ·
              refine ⟨1181345695784171087493557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787563797189447391662371 1181345695784171087493557)
              ·
                refine ⟨110751158979766039452521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1181345695784171087493557 110751158979766039452521)
                ·
                  rfl

theorem cell19_363972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_363972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363972 prefixEnd_363972 := by exact prefixLift 363972
  have htrace : WordTrace (prefixWord ++ tailWord_363972) baseStart_363972 baseEnd_363972 := by
    simpa [prefixWord, tailWord_363972, baseEnd_363972] using wordTrace_append hprefix tailTrace_363972
  have hstable : (prefixWord ++ tailWord_363972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363972).length < 2 ^ (prefixWord ++ tailWord_363972).sum := by decide
  have hdescent : baseEnd_363972 < baseStart_363972 := by decide
  rcases family_descends (prefixWord ++ tailWord_363972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363993 : List Nat := [1, 2, 1, 2, 4, 4, 5]
def baseStart_363993 : Nat := 118140960795 + 363993 * 2 ^ 59
def prefixEnd_363993 : Nat := 4983230072969 + 3 ^ 40 * 363993 * 2
def baseEnd_363993 : Nat := 36919182987081404328599

theorem tailTrace_363993 : CollatzResearch.WordTrace tailWord_363993 prefixEnd_363993 36919182987081404328599 := by
  unfold tailWord_363993
  simp only [CollatzResearch.WordTrace]
  refine ⟨13275915370323000900296633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8850610246882000600197755 13275915370323000900296633)
  ·
    refine ⟨9956936527742250675222475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13275915370323000900296633 9956936527742250675222475)
    ·
      refine ⟨14935404791613376012833713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9956936527742250675222475 14935404791613376012833713)
      ·
        refine ⟨11201553593710032009625285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14935404791613376012833713 11201553593710032009625285)
        ·
          refine ⟨2100291298820631001804741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11201553593710032009625285 2100291298820631001804741)
          ·
            refine ⟨393804618528868312838389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2100291298820631001804741 393804618528868312838389)
            ·
              refine ⟨36919182987081404328599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 393804618528868312838389 36919182987081404328599)
              ·
                rfl

theorem cell19_363993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_363993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_363993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_363993 prefixEnd_363993 := by exact prefixLift 363993
  have htrace : WordTrace (prefixWord ++ tailWord_363993) baseStart_363993 baseEnd_363993 := by
    simpa [prefixWord, tailWord_363993, baseEnd_363993] using wordTrace_append hprefix tailTrace_363993
  have hstable : (prefixWord ++ tailWord_363993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363993).length < 2 ^ (prefixWord ++ tailWord_363993).sum := by decide
  have hdescent : baseEnd_363993 < baseStart_363993 := by decide
  rcases family_descends (prefixWord ++ tailWord_363993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364010 : List Nat := [3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_364010 : Nat := 118140960795 + 364010 * 2 ^ 59
def prefixEnd_364010 : Nat := 4983230072969 + 3 ^ 40 * 364010 * 2
def baseEnd_364010 : Nat := 110762721803393210607973

theorem tailTrace_364010 : CollatzResearch.WordTrace tailWord_364010 prefixEnd_364010 110762721803393210607973 := by
  unfold tailWord_364010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3319133852815353200916371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8851023607507608535776989 3319133852815353200916371)
  ·
    refine ⟨4978700779223029801374557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3319133852815353200916371 4978700779223029801374557)
    ·
      refine ⟨1867012792208636175515459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4978700779223029801374557 1867012792208636175515459)
      ·
        refine ⟨2800519188312954263273189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867012792208636175515459 2800519188312954263273189)
        ·
          refine ⟨525097347808678924363723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2800519188312954263273189 525097347808678924363723)
          ·
            refine ⟨787646021713018386545585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525097347808678924363723 787646021713018386545585)
            ·
              refine ⟨590734516284763789909189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787646021713018386545585 590734516284763789909189)
              ·
                refine ⟨110762721803393210607973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590734516284763789909189 110762721803393210607973)
                ·
                  rfl

theorem cell19_364010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_364010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364010 prefixEnd_364010 := by exact prefixLift 364010
  have htrace : WordTrace (prefixWord ++ tailWord_364010) baseStart_364010 baseEnd_364010 := by
    simpa [prefixWord, tailWord_364010, baseEnd_364010] using wordTrace_append hprefix tailTrace_364010
  have hstable : (prefixWord ++ tailWord_364010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364010).length < 2 ^ (prefixWord ++ tailWord_364010).sum := by decide
  have hdescent : baseEnd_364010 < baseStart_364010 := by decide
  rcases family_descends (prefixWord ++ tailWord_364010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364067 : List Nat := [1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_364067 : Nat := 118140960795 + 364067 * 2 ^ 59
def prefixEnd_364067 : Nat := 4983230072969 + 3 ^ 40 * 364067 * 2
def baseEnd_364067 : Nat := 110780066038833967341151

theorem tailTrace_364067 : CollatzResearch.WordTrace tailWord_364067 prefixEnd_364067 110780066038833967341151 := by
  unfold tailWord_364067
  simp only [CollatzResearch.WordTrace]
  refine ⟨13278614372054911538490455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8852409581369941025660303 13278614372054911538490455)
  ·
    refine ⟨19917921558082367307735683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13278614372054911538490455 19917921558082367307735683)
    ·
      refine ⟨29876882337123550961603525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19917921558082367307735683 29876882337123550961603525)
      ·
        refine ⟨5601915438210665805300661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29876882337123550961603525 5601915438210665805300661)
        ·
          refine ⟨525179572332249919246937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5601915438210665805300661 525179572332249919246937)
          ·
            refine ⟨393884679249187439435203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525179572332249919246937 393884679249187439435203)
            ·
              refine ⟨590827018873781159152805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393884679249187439435203 590827018873781159152805)
              ·
                refine ⟨110780066038833967341151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590827018873781159152805 110780066038833967341151)
                ·
                  rfl

theorem cell19_364067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_364067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364067 prefixEnd_364067 := by exact prefixLift 364067
  have htrace : WordTrace (prefixWord ++ tailWord_364067) baseStart_364067 baseEnd_364067 := by
    simpa [prefixWord, tailWord_364067, baseEnd_364067] using wordTrace_append hprefix tailTrace_364067
  have hstable : (prefixWord ++ tailWord_364067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364067).length < 2 ^ (prefixWord ++ tailWord_364067).sum := by decide
  have hdescent : baseEnd_364067 < baseStart_364067 := by decide
  rcases family_descends (prefixWord ++ tailWord_364067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364128 : List Nat := [2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_364128 : Nat := 118140960795 + 364128 * 2 ^ 59
def prefixEnd_364128 : Nat := 4983230072969 + 3 ^ 40 * 364128 * 2
def baseEnd_364128 : Nat := 110798627413603899985429

theorem tailTrace_364128 : CollatzResearch.WordTrace tailWord_364128 prefixEnd_364128 110798627413603899985429 := by
  unfold tailWord_364128
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640419612416959478230519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8853892816555945970974025 6640419612416959478230519)
  ·
    refine ⟨9960629418625439217345779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6640419612416959478230519 9960629418625439217345779)
    ·
      refine ⟨14940944127938158826018669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9960629418625439217345779 14940944127938158826018669)
      ·
        refine ⟨5602854047976809559757001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14940944127938158826018669 5602854047976809559757001)
        ·
          refine ⟨4202140535982607169817751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5602854047976809559757001 4202140535982607169817751)
          ·
            refine ⟨6303210803973910754726627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202140535982607169817751 6303210803973910754726627)
            ·
              refine ⟨9454816205960866132089941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6303210803973910754726627 9454816205960866132089941)
              ·
                refine ⟨110798627413603899985429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9454816205960866132089941 110798627413603899985429)
                ·
                  rfl

theorem cell19_364128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_364128 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364128 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364128 prefixEnd_364128 := by exact prefixLift 364128
  have htrace : WordTrace (prefixWord ++ tailWord_364128) baseStart_364128 baseEnd_364128 := by
    simpa [prefixWord, tailWord_364128, baseEnd_364128] using wordTrace_append hprefix tailTrace_364128
  have hstable : (prefixWord ++ tailWord_364128).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364128).length < 2 ^ (prefixWord ++ tailWord_364128).sum := by decide
  have hdescent : baseEnd_364128 < baseStart_364128 := by decide
  rcases family_descends (prefixWord ++ tailWord_364128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364141 : List Nat := [1, 5, 1, 1, 4, 2, 2, 3]
def baseStart_364141 : Nat := 118140960795 + 364141 * 2 ^ 59
def prefixEnd_364141 : Nat := 4983230072969 + 3 ^ 40 * 364141 * 2
def baseEnd_364141 : Nat := 110802583116423721696505

theorem tailTrace_364141 : CollatzResearch.WordTrace tailWord_364141 prefixEnd_364141 110802583116423721696505 := by
  unfold tailWord_364141
  simp only [CollatzResearch.WordTrace]
  refine ⟨13281313373786822176684277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8854208915857881451122851 13281313373786822176684277)
  ·
    refine ⟨1245123128792514579064151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13281313373786822176684277 1245123128792514579064151)
    ·
      refine ⟨1867684693188771868596227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245123128792514579064151 1867684693188771868596227)
      ·
        refine ⟨2801527039783157802894341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867684693188771868596227 2801527039783157802894341)
        ·
          refine ⟨525286319959342088042689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2801527039783157802894341 525286319959342088042689)
          ·
            refine ⟨393964739969506566032017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525286319959342088042689 393964739969506566032017)
            ·
              refine ⟨295473554977129924524013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393964739969506566032017 295473554977129924524013)
              ·
                refine ⟨110802583116423721696505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295473554977129924524013 110802583116423721696505)
                ·
                  rfl

theorem cell19_364141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_364141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364141 prefixEnd_364141 := by exact prefixLift 364141
  have htrace : WordTrace (prefixWord ++ tailWord_364141) baseStart_364141 baseEnd_364141 := by
    simpa [prefixWord, tailWord_364141, baseEnd_364141] using wordTrace_append hprefix tailTrace_364141
  have hstable : (prefixWord ++ tailWord_364141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364141).length < 2 ^ (prefixWord ++ tailWord_364141).sum := by decide
  have hdescent : baseEnd_364141 < baseStart_364141 := by decide
  rcases family_descends (prefixWord ++ tailWord_364141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364183 : List Nat := [1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_364183 : Nat := 118140960795 + 364183 * 2 ^ 59
def prefixEnd_364183 : Nat := 4983230072969 + 3 ^ 40 * 364183 * 2
def baseEnd_364183 : Nat := 110815363079380068763057

theorem tailTrace_364183 : CollatzResearch.WordTrace tailWord_364183 prefixEnd_364183 110815363079380068763057 := by
  unfold tailWord_364183
  simp only [CollatzResearch.WordTrace]
  refine ⟨13282845239634663349713203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8855230159756442233142135 13282845239634663349713203)
  ·
    refine ⟨19924267859451995024569805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13282845239634663349713203 19924267859451995024569805)
    ·
      refine ⟨7471600447294498134213677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19924267859451995024569805 7471600447294498134213677)
      ·
        refine ⟨2801850167735436800330129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7471600447294498134213677 2801850167735436800330129)
        ·
          refine ⟨2101387625801577600247597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2801850167735436800330129 2101387625801577600247597)
          ·
            refine ⟨788020359675591600092849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2101387625801577600247597 788020359675591600092849)
            ·
              refine ⟨591015269756693700069637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788020359675591600092849 591015269756693700069637)
              ·
                refine ⟨110815363079380068763057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591015269756693700069637 110815363079380068763057)
                ·
                  rfl

theorem cell19_364183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_364183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364183 prefixEnd_364183 := by exact prefixLift 364183
  have htrace : WordTrace (prefixWord ++ tailWord_364183) baseStart_364183 baseEnd_364183 := by
    simpa [prefixWord, tailWord_364183, baseEnd_364183] using wordTrace_append hprefix tailTrace_364183
  have hstable : (prefixWord ++ tailWord_364183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364183).length < 2 ^ (prefixWord ++ tailWord_364183).sum := by decide
  have hdescent : baseEnd_364183 < baseStart_364183 := by decide
  rcases family_descends (prefixWord ++ tailWord_364183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364236 : List Nat := [2, 2, 1, 5, 3, 1, 1, 4]
def baseStart_364236 : Nat := 118140960795 + 364236 * 2 ^ 59
def prefixEnd_364236 : Nat := 4983230072969 + 3 ^ 40 * 364236 * 2
def baseEnd_364236 : Nat := 110831490175491649585135

theorem tailTrace_364236 : CollatzResearch.WordTrace tailWord_364236 prefixEnd_364236 110831490175491649585135 := by
  unfold tailWord_364236
  simp only [CollatzResearch.WordTrace]
  refine ⟨6642389154221326700696281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8856518872295102267595041 6642389154221326700696281)
  ·
    refine ⟨4981791865665995025522211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6642389154221326700696281 4981791865665995025522211)
    ·
      refine ⟨7472687798498992538283317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4981791865665995025522211 7472687798498992538283317)
      ·
        refine ⟨700564481109280550464061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7472687798498992538283317 700564481109280550464061)
        ·
          refine ⟨262711680415980206424023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 700564481109280550464061 262711680415980206424023)
          ·
            refine ⟨394067520623970309636035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262711680415980206424023 394067520623970309636035)
            ·
              refine ⟨591101280935955464454053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394067520623970309636035 591101280935955464454053)
              ·
                refine ⟨110831490175491649585135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591101280935955464454053 110831490175491649585135)
                ·
                  rfl

theorem cell19_364236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_364236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364236 prefixEnd_364236 := by exact prefixLift 364236
  have htrace : WordTrace (prefixWord ++ tailWord_364236) baseStart_364236 baseEnd_364236 := by
    simpa [prefixWord, tailWord_364236, baseEnd_364236] using wordTrace_append hprefix tailTrace_364236
  have hstable : (prefixWord ++ tailWord_364236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364236).length < 2 ^ (prefixWord ++ tailWord_364236).sum := by decide
  have hdescent : baseEnd_364236 < baseStart_364236 := by decide
  rcases family_descends (prefixWord ++ tailWord_364236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364257 : List Nat := [1, 2, 3, 1, 5, 1, 3, 3]
def baseStart_364257 : Nat := 118140960795 + 364257 * 2 ^ 59
def prefixEnd_364257 : Nat := 4983230072969 + 3 ^ 40 * 364257 * 2
def baseEnd_364257 : Nat := 110837880156969823118411

theorem tailTrace_364257 : CollatzResearch.WordTrace tailWord_364257 prefixEnd_364257 110837880156969823118411 := by
  unfold tailWord_364257
  simp only [CollatzResearch.WordTrace]
  refine ⟨13285544241366573987907025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8857029494244382658604683 13285544241366573987907025)
  ·
    refine ⟨9964158181024930490930269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13285544241366573987907025 9964158181024930490930269)
    ·
      refine ⟨3736559317884348934098851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9964158181024930490930269 3736559317884348934098851)
      ·
        refine ⟨5604838976826523401148277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3736559317884348934098851 5604838976826523401148277)
        ·
          refine ⟨525453654077486568857651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5604838976826523401148277 525453654077486568857651)
          ·
            refine ⟨788180481116229853286477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525453654077486568857651 788180481116229853286477)
            ·
              refine ⟨295567680418586194982429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 788180481116229853286477 295567680418586194982429)
              ·
                refine ⟨110837880156969823118411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295567680418586194982429 110837880156969823118411)
                ·
                  rfl

theorem cell19_364257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_364257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364257 prefixEnd_364257 := by exact prefixLift 364257
  have htrace : WordTrace (prefixWord ++ tailWord_364257) baseStart_364257 baseEnd_364257 := by
    simpa [prefixWord, tailWord_364257, baseEnd_364257] using wordTrace_append hprefix tailTrace_364257
  have hstable : (prefixWord ++ tailWord_364257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364257).length < 2 ^ (prefixWord ++ tailWord_364257).sum := by decide
  have hdescent : baseEnd_364257 < baseStart_364257 := by decide
  rcases family_descends (prefixWord ++ tailWord_364257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364278 : List Nat := [5, 1, 1, 1, 1, 4, 6]
def baseStart_364278 : Nat := 118140960795 + 364278 * 2 ^ 59
def prefixEnd_364278 : Nat := 4983230072969 + 3 ^ 40 * 364278 * 2
def baseEnd_364278 : Nat := 36948090046149332217229

theorem tailTrace_364278 : CollatzResearch.WordTrace tailWord_364278 prefixEnd_364278 36948090046149332217229 := by
  unfold tailWord_364278
  simp only [CollatzResearch.WordTrace]
  refine ⟨830394385893155910901343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8857540116193663049614325 830394385893155910901343)
  ·
    refine ⟨1245591578839733866352015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 830394385893155910901343 1245591578839733866352015)
    ·
      refine ⟨1868387368259600799528023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245591578839733866352015 1868387368259600799528023)
      ·
        refine ⟨2802581052389401199292035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868387368259600799528023 2802581052389401199292035)
        ·
          refine ⟨4203871578584101798938053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802581052389401199292035 4203871578584101798938053)
          ·
            refine ⟨788225920984519087300885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4203871578584101798938053 788225920984519087300885)
            ·
              refine ⟨36948090046149332217229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 788225920984519087300885 36948090046149332217229)
              ·
                rfl

theorem cell19_364278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_364278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364278 prefixEnd_364278 := by exact prefixLift 364278
  have htrace : WordTrace (prefixWord ++ tailWord_364278) baseStart_364278 baseEnd_364278 := by
    simpa [prefixWord, tailWord_364278, baseEnd_364278] using wordTrace_append hprefix tailTrace_364278
  have hstable : (prefixWord ++ tailWord_364278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364278).length < 2 ^ (prefixWord ++ tailWord_364278).sum := by decide
  have hdescent : baseEnd_364278 < baseStart_364278 := by decide
  rcases family_descends (prefixWord ++ tailWord_364278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364308 : List Nat := [2, 4, 4, 1, 1, 2, 2, 3]
def baseStart_364308 : Nat := 118140960795 + 364308 * 2 ^ 59
def prefixEnd_364308 : Nat := 4983230072969 + 3 ^ 40 * 364308 * 2
def baseEnd_364308 : Nat := 110853398683416815984939

theorem tailTrace_364308 : CollatzResearch.WordTrace tailWord_364308 prefixEnd_364308 110853398683416815984939 := by
  unfold tailWord_364308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6643702182090904849006789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8858269576121206465342385 6643702182090904849006789)
  ·
    refine ⟨1245694159142044659188773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6643702182090904849006789 1245694159142044659188773)
    ·
      refine ⟨233567654839133373597895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1245694159142044659188773 233567654839133373597895)
      ·
        refine ⟨350351482258700060396843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233567654839133373597895 350351482258700060396843)
        ·
          refine ⟨525527223388050090595265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350351482258700060396843 525527223388050090595265)
          ·
            refine ⟨394145417541037567946449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525527223388050090595265 394145417541037567946449)
            ·
              refine ⟨295609063155778175959837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394145417541037567946449 295609063155778175959837)
              ·
                refine ⟨110853398683416815984939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295609063155778175959837 110853398683416815984939)
                ·
                  rfl

theorem cell19_364308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_364308 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364308 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364308 prefixEnd_364308 := by exact prefixLift 364308
  have htrace : WordTrace (prefixWord ++ tailWord_364308) baseStart_364308 baseEnd_364308 := by
    simpa [prefixWord, tailWord_364308, baseEnd_364308] using wordTrace_append hprefix tailTrace_364308
  have hstable : (prefixWord ++ tailWord_364308).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364308).length < 2 ^ (prefixWord ++ tailWord_364308).sum := by decide
  have hdescent : baseEnd_364308 < baseStart_364308 := by decide
  rcases family_descends (prefixWord ++ tailWord_364308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364314 : List Nat := [3, 1, 1, 3, 2, 4, 2, 3]
def baseStart_364314 : Nat := 118140960795 + 364314 * 2 ^ 59
def prefixEnd_364314 : Nat := 4983230072969 + 3 ^ 40 * 364314 * 2
def baseEnd_364314 : Nat := 110855224392410579851589

theorem tailTrace_364314 : CollatzResearch.WordTrace tailWord_364314 prefixEnd_364314 110855224392410579851589 := by
  unfold tailWord_364314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3321905800540018180682999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8858415468106715148487997 3321905800540018180682999)
  ·
    refine ⟨4982858700810027271024499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3321905800540018180682999 4982858700810027271024499)
    ·
      refine ⟨7474288051215040906536749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4982858700810027271024499 7474288051215040906536749)
      ·
        refine ⟨2802858019205640339951281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7474288051215040906536749 2802858019205640339951281)
        ·
          refine ⟨2102143514404230254963461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2802858019205640339951281 2102143514404230254963461)
          ·
            refine ⟨394151908950793172805649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2102143514404230254963461 394151908950793172805649)
            ·
              refine ⟨295613931713094879604237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394151908950793172805649 295613931713094879604237)
              ·
                refine ⟨110855224392410579851589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295613931713094879604237 110855224392410579851589)
                ·
                  rfl

theorem cell19_364314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_364314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364314 prefixEnd_364314 := by exact prefixLift 364314
  have htrace : WordTrace (prefixWord ++ tailWord_364314) baseStart_364314 baseEnd_364314 := by
    simpa [prefixWord, tailWord_364314, baseEnd_364314] using wordTrace_append hprefix tailTrace_364314
  have hstable : (prefixWord ++ tailWord_364314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364314).length < 2 ^ (prefixWord ++ tailWord_364314).sum := by decide
  have hdescent : baseEnd_364314 < baseStart_364314 := by decide
  rcases family_descends (prefixWord ++ tailWord_364314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364337 : List Nat := [1, 2, 2, 3, 2, 2, 7]
def baseStart_364337 : Nat := 118140960795 + 364337 * 2 ^ 59
def prefixEnd_364337 : Nat := 4983230072969 + 3 ^ 40 * 364337 * 2
def baseEnd_364337 : Nat := 36954074314517780446805

theorem tailTrace_364337 : CollatzResearch.WordTrace tailWord_364337 prefixEnd_364337 36954074314517780446805 := by
  unfold tailWord_364337
  simp only [CollatzResearch.WordTrace]
  refine ⟨13288462081076747650819265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8858974720717831767212843 13288462081076747650819265)
  ·
    refine ⟨9966346560807560738114449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13288462081076747650819265 9966346560807560738114449)
    ·
      refine ⟨7474759920605670553585837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9966346560807560738114449 7474759920605670553585837)
      ·
        refine ⟨2803034970227126457594689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7474759920605670553585837 2803034970227126457594689)
        ·
          refine ⟨2102276227670344843196017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2803034970227126457594689 2102276227670344843196017)
          ·
            refine ⟨1576707170752758632397013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2102276227670344843196017 1576707170752758632397013)
            ·
              refine ⟨36954074314517780446805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1576707170752758632397013 36954074314517780446805)
              ·
                rfl

theorem cell19_364337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_364337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364337 prefixEnd_364337 := by exact prefixLift 364337
  have htrace : WordTrace (prefixWord ++ tailWord_364337) baseStart_364337 baseEnd_364337 := by
    simpa [prefixWord, tailWord_364337, baseEnd_364337] using wordTrace_append hprefix tailTrace_364337
  have hstable : (prefixWord ++ tailWord_364337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364337).length < 2 ^ (prefixWord ++ tailWord_364337).sum := by decide
  have hdescent : baseEnd_364337 < baseStart_364337 := by decide
  rcases family_descends (prefixWord ++ tailWord_364337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364449 : List Nat := [1, 2, 3, 4, 2, 1, 6]
def baseStart_364449 : Nat := 118140960795 + 364449 * 2 ^ 59
def prefixEnd_364449 : Nat := 4983230072969 + 3 ^ 40 * 364449 * 2
def baseEnd_364449 : Nat := 36965434281590088950407

theorem tailTrace_364449 : CollatzResearch.WordTrace tailWord_364449 prefixEnd_364449 36965434281590088950407 := by
  unfold tailWord_364449
  simp only [CollatzResearch.WordTrace]
  refine ⟨13292547056670990778896401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8861698037780660519264267 13292547056670990778896401)
  ·
    refine ⟨9969410292503243084172301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13292547056670990778896401 9969410292503243084172301)
    ·
      refine ⟨3738528859688716156564613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9969410292503243084172301 3738528859688716156564613)
      ·
        refine ⟨700974161191634279355865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3738528859688716156564613 700974161191634279355865)
        ·
          refine ⟨525730620893725709516899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 700974161191634279355865 525730620893725709516899)
          ·
            refine ⟨788595931340588564275349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525730620893725709516899 788595931340588564275349)
            ·
              refine ⟨36965434281590088950407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 788595931340588564275349 36965434281590088950407)
              ·
                rfl

theorem cell19_364449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_364449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364449 prefixEnd_364449 := by exact prefixLift 364449
  have htrace : WordTrace (prefixWord ++ tailWord_364449) baseStart_364449 baseEnd_364449 := by
    simpa [prefixWord, tailWord_364449, baseEnd_364449] using wordTrace_append hprefix tailTrace_364449
  have hstable : (prefixWord ++ tailWord_364449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364449).length < 2 ^ (prefixWord ++ tailWord_364449).sum := by decide
  have hdescent : baseEnd_364449 < baseStart_364449 := by decide
  rcases family_descends (prefixWord ++ tailWord_364449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364502 : List Nat := [5, 2, 1, 1, 4, 1, 5]
def baseStart_364502 : Nat := 118140960795 + 364502 * 2 ^ 59
def prefixEnd_364502 : Nat := 4983230072969 + 3 ^ 40 * 364502 * 2
def baseEnd_364502 : Nat := 36970809980293949224433

theorem tailTrace_364502 : CollatzResearch.WordTrace tailWord_364502 prefixEnd_364502 36970809980293949224433 := by
  unfold tailWord_364502
  simp only [CollatzResearch.WordTrace]
  refine ⟨830905007842436301910985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8862986750319320553717173 830905007842436301910985)
  ·
    refine ⟨623178755881827226433239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 830905007842436301910985 623178755881827226433239)
    ·
      refine ⟨934768133822740839649859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623178755881827226433239 934768133822740839649859)
      ·
        refine ⟨1402152200734111259474789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934768133822740839649859 1402152200734111259474789)
        ·
          refine ⟨262903537637645861151523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1402152200734111259474789 262903537637645861151523)
          ·
            refine ⟨394355306456468791727285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262903537637645861151523 394355306456468791727285)
            ·
              refine ⟨36970809980293949224433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 394355306456468791727285 36970809980293949224433)
              ·
                rfl

theorem cell19_364502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 5].length) (baseStart_364502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364502 prefixEnd_364502 := by exact prefixLift 364502
  have htrace : WordTrace (prefixWord ++ tailWord_364502) baseStart_364502 baseEnd_364502 := by
    simpa [prefixWord, tailWord_364502, baseEnd_364502] using wordTrace_append hprefix tailTrace_364502
  have hstable : (prefixWord ++ tailWord_364502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364502).length < 2 ^ (prefixWord ++ tailWord_364502).sum := by decide
  have hdescent : baseEnd_364502 < baseStart_364502 := by decide
  rcases family_descends (prefixWord ++ tailWord_364502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364506 : List Nat := [3, 1, 1, 2, 5, 2, 5]
def baseStart_364506 : Nat := 118140960795 + 364506 * 2 ^ 59
def prefixEnd_364506 : Nat := 4983230072969 + 3 ^ 40 * 364506 * 2
def baseEnd_364506 : Nat := 36971215693403674528133

theorem tailTrace_364506 : CollatzResearch.WordTrace tailWord_364506 prefixEnd_364506 36971215693403674528133 := by
  unfold tailWord_364506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323656504366122378430343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8863084011642993009147581 3323656504366122378430343)
  ·
    refine ⟨4985484756549183567645515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3323656504366122378430343 4985484756549183567645515)
    ·
      refine ⟨7478227134823775351468273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4985484756549183567645515 7478227134823775351468273)
      ·
        refine ⟨5608670351117831513601205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7478227134823775351468273 5608670351117831513601205)
        ·
          refine ⟨525812845417296704400113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5608670351117831513601205 525812845417296704400113)
          ·
            refine ⟨394359634062972528300085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525812845417296704400113 394359634062972528300085)
            ·
              refine ⟨36971215693403674528133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 394359634062972528300085 36971215693403674528133)
              ·
                rfl

theorem cell19_364506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_364506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364506 prefixEnd_364506 := by exact prefixLift 364506
  have htrace : WordTrace (prefixWord ++ tailWord_364506) baseStart_364506 baseEnd_364506 := by
    simpa [prefixWord, tailWord_364506, baseEnd_364506] using wordTrace_append hprefix tailTrace_364506
  have hstable : (prefixWord ++ tailWord_364506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364506).length < 2 ^ (prefixWord ++ tailWord_364506).sum := by decide
  have hdescent : baseEnd_364506 < baseStart_364506 := by decide
  rcases family_descends (prefixWord ++ tailWord_364506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364527 : List Nat := [1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_364527 : Nat := 118140960795 + 364527 * 2 ^ 59
def prefixEnd_364527 : Nat := 4983230072969 + 3 ^ 40 * 364527 * 2
def baseEnd_364527 : Nat := 110920037061689197117675

theorem tailTrace_364527 : CollatzResearch.WordTrace tailWord_364527 prefixEnd_364527 110920037061689197117675 := by
  unfold tailWord_364527
  simp only [CollatzResearch.WordTrace]
  refine ⟨13295391950388410100235835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8863594633592273400157223 13295391950388410100235835)
  ·
    refine ⟨19943087925582615150353753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13295391950388410100235835 19943087925582615150353753)
    ·
      refine ⟨14957315944186961362765315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19943087925582615150353753 14957315944186961362765315)
      ·
        refine ⟨22435973916280442044147973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14957315944186961362765315 22435973916280442044147973)
        ·
          refine ⟨4206745109302582883277745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22435973916280442044147973 4206745109302582883277745)
          ·
            refine ⟨3155058831976937162458309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4206745109302582883277745 3155058831976937162458309)
            ·
              refine ⟨591573530995675717960933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3155058831976937162458309 591573530995675717960933)
              ·
                refine ⟨110920037061689197117675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591573530995675717960933 110920037061689197117675)
                ·
                  rfl

theorem cell19_364527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_364527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364527 prefixEnd_364527 := by exact prefixLift 364527
  have htrace : WordTrace (prefixWord ++ tailWord_364527) baseStart_364527 baseEnd_364527 := by
    simpa [prefixWord, tailWord_364527, baseEnd_364527] using wordTrace_append hprefix tailTrace_364527
  have hstable : (prefixWord ++ tailWord_364527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364527).length < 2 ^ (prefixWord ++ tailWord_364527).sum := by decide
  have hdescent : baseEnd_364527 < baseStart_364527 := by decide
  rcases family_descends (prefixWord ++ tailWord_364527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364565 : List Nat := [1, 3, 2, 1, 5, 7]
def baseStart_364565 : Nat := 118140960795 + 364565 * 2 ^ 59
def prefixEnd_364565 : Nat := 4983230072969 + 3 ^ 40 * 364565 * 2
def baseEnd_364565 : Nat := 12325733320590707585903

theorem tailTrace_364565 : CollatzResearch.WordTrace tailWord_364565 prefixEnd_364565 12325733320590707585903 := by
  unfold tailWord_364565
  simp only [CollatzResearch.WordTrace]
  refine ⟨13296777924250742590119149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8864518616167161726746099 13296777924250742590119149)
  ·
    refine ⟨4986291721594028471294681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13296777924250742590119149 4986291721594028471294681)
    ·
      refine ⟨3739718791195521353471011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4986291721594028471294681 3739718791195521353471011)
      ·
        refine ⟨5609578186793282030206517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739718791195521353471011 5609578186793282030206517)
        ·
          refine ⟨525897955011870190331861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5609578186793282030206517 525897955011870190331861)
          ·
            refine ⟨12325733320590707585903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 525897955011870190331861 12325733320590707585903)
            ·
              rfl

theorem cell19_364565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 7].length) (baseStart_364565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364565 prefixEnd_364565 := by exact prefixLift 364565
  have htrace : WordTrace (prefixWord ++ tailWord_364565) baseStart_364565 baseEnd_364565 := by
    simpa [prefixWord, tailWord_364565, baseEnd_364565] using wordTrace_append hprefix tailTrace_364565
  have hstable : (prefixWord ++ tailWord_364565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364565).length < 2 ^ (prefixWord ++ tailWord_364565).sum := by decide
  have hdescent : baseEnd_364565 < baseStart_364565 := by decide
  rcases family_descends (prefixWord ++ tailWord_364565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364580 : List Nat := [2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_364580 : Nat := 118140960795 + 364580 * 2 ^ 59
def prefixEnd_364580 : Nat := 4983230072969 + 3 ^ 40 * 364580 * 2
def baseEnd_364580 : Nat := 110936164157800777939753

theorem tailTrace_364580 : CollatzResearch.WordTrace tailWord_364580 prefixEnd_364580 110936164157800777939753 := by
  unfold tailWord_364580
  simp only [CollatzResearch.WordTrace]
  refine ⟨6648662509598200075957597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8864883346130933434610129 6648662509598200075957597)
  ·
    refine ⟨2493248441099325028484099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6648662509598200075957597 2493248441099325028484099)
    ·
      refine ⟨3739872661648987542726149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493248441099325028484099 3739872661648987542726149)
      ·
        refine ⟨701226124059185164261153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3739872661648987542726149 701226124059185164261153)
        ·
          refine ⟨525919593044388873195865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701226124059185164261153 525919593044388873195865)
          ·
            refine ⟨394439694783291654896899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525919593044388873195865 394439694783291654896899)
            ·
              refine ⟨591659542174937482345349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394439694783291654896899 591659542174937482345349)
              ·
                refine ⟨110936164157800777939753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591659542174937482345349 110936164157800777939753)
                ·
                  rfl

theorem cell19_364580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_364580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364580 prefixEnd_364580 := by exact prefixLift 364580
  have htrace : WordTrace (prefixWord ++ tailWord_364580) baseStart_364580 baseEnd_364580 := by
    simpa [prefixWord, tailWord_364580, baseEnd_364580] using wordTrace_append hprefix tailTrace_364580
  have hstable : (prefixWord ++ tailWord_364580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364580).length < 2 ^ (prefixWord ++ tailWord_364580).sum := by decide
  have hdescent : baseEnd_364580 < baseStart_364580 := by decide
  rcases family_descends (prefixWord ++ tailWord_364580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364622 : List Nat := [4, 1, 1, 1, 1, 5, 6]
def baseStart_364622 : Nat := 118140960795 + 364622 * 2 ^ 59
def prefixEnd_364622 : Nat := 4983230072969 + 3 ^ 40 * 364622 * 2
def baseEnd_364622 : Nat := 36982981373585708335435

theorem tailTrace_364622 : CollatzResearch.WordTrace tailWord_364622 prefixEnd_364622 36982981373585708335435 := by
  unfold tailWord_364622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662357110630530165618015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8865904590029494216629413 1662357110630530165618015)
  ·
    refine ⟨2493535665945795248427023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1662357110630530165618015 2493535665945795248427023)
    ·
      refine ⟨3740303498918692872640535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493535665945795248427023 3740303498918692872640535)
      ·
        refine ⟨5610455248378039308960803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740303498918692872640535 5610455248378039308960803)
        ·
          refine ⟨8415682872567058963441205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5610455248378039308960803 8415682872567058963441205)
          ·
            refine ⟨788970269303161777822613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8415682872567058963441205 788970269303161777822613)
            ·
              refine ⟨36982981373585708335435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 788970269303161777822613 36982981373585708335435)
              ·
                rfl

theorem cell19_364622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_364622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364622 prefixEnd_364622 := by exact prefixLift 364622
  have htrace : WordTrace (prefixWord ++ tailWord_364622) baseStart_364622 baseEnd_364622 := by
    simpa [prefixWord, tailWord_364622, baseEnd_364622] using wordTrace_append hprefix tailTrace_364622
  have hstable : (prefixWord ++ tailWord_364622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364622).length < 2 ^ (prefixWord ++ tailWord_364622).sum := by decide
  have hdescent : baseEnd_364622 < baseStart_364622 := by decide
  rcases family_descends (prefixWord ++ tailWord_364622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364658 : List Nat := [3, 2, 1, 2, 2, 2, 4, 3]
def baseStart_364658 : Nat := 118140960795 + 364658 * 2 ^ 59
def prefixEnd_364658 : Nat := 4983230072969 + 3 ^ 40 * 364658 * 2
def baseEnd_364658 : Nat := 110959898374719708206207

theorem tailTrace_364658 : CollatzResearch.WordTrace tailWord_364658 prefixEnd_364658 110959898374719708206207 := by
  unfold tailWord_364658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3325042478228454868313657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8866779941942546315503085 3325042478228454868313657)
  ·
    refine ⟨2493781858671341151235243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3325042478228454868313657 2493781858671341151235243)
    ·
      refine ⟨3740672788007011726852865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493781858671341151235243 3740672788007011726852865)
      ·
        refine ⟨2805504591005258795139649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3740672788007011726852865 2805504591005258795139649)
        ·
          refine ⟨2104128443253944096354737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2805504591005258795139649 2104128443253944096354737)
          ·
            refine ⟨1578096332440458072266053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2104128443253944096354737 1578096332440458072266053)
            ·
              refine ⟨295893062332585888549885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1578096332440458072266053 295893062332585888549885)
              ·
                refine ⟨110959898374719708206207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295893062332585888549885 110959898374719708206207)
                ·
                  rfl

theorem cell19_364658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_364658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364658 prefixEnd_364658 := by exact prefixLift 364658
  have htrace : WordTrace (prefixWord ++ tailWord_364658) baseStart_364658 baseEnd_364658 := by
    simpa [prefixWord, tailWord_364658, baseEnd_364658] using wordTrace_append hprefix tailTrace_364658
  have hstable : (prefixWord ++ tailWord_364658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364658).length < 2 ^ (prefixWord ++ tailWord_364658).sum := by decide
  have hdescent : baseEnd_364658 < baseStart_364658 := by decide
  rcases family_descends (prefixWord ++ tailWord_364658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364696 : List Nat := [2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_364696 : Nat := 118140960795 + 364696 * 2 ^ 59
def prefixEnd_364696 : Nat := 4983230072969 + 3 ^ 40 * 364696 * 2
def baseEnd_364696 : Nat := 110971461198346879361659

theorem tailTrace_364696 : CollatzResearch.WordTrace tailWord_364696 prefixEnd_364696 110971461198346879361659 := by
  unfold tailWord_364696
  simp only [CollatzResearch.WordTrace]
  refine ⟨6650777943388075981568971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8867703924517434642091961 6650777943388075981568971)
  ·
    refine ⟨9976166915082113972353457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6650777943388075981568971 9976166915082113972353457)
    ·
      refine ⟨7482125186311585479265093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9976166915082113972353457 7482125186311585479265093)
      ·
        refine ⟨1402898472433422277362205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7482125186311585479265093 1402898472433422277362205)
        ·
          refine ⟨526086927162533354010827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1402898472433422277362205 526086927162533354010827)
          ·
            refine ⟨789130390743800031016241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526086927162533354010827 789130390743800031016241)
            ·
              refine ⟨591847793057850023262181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789130390743800031016241 591847793057850023262181)
              ·
                refine ⟨110971461198346879361659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591847793057850023262181 110971461198346879361659)
                ·
                  rfl

theorem cell19_364696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_364696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364696 prefixEnd_364696 := by exact prefixLift 364696
  have htrace : WordTrace (prefixWord ++ tailWord_364696) baseStart_364696 baseEnd_364696 := by
    simpa [prefixWord, tailWord_364696, baseEnd_364696] using wordTrace_append hprefix tailTrace_364696
  have hstable : (prefixWord ++ tailWord_364696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364696).length < 2 ^ (prefixWord ++ tailWord_364696).sum := by decide
  have hdescent : baseEnd_364696 < baseStart_364696 := by decide
  rcases family_descends (prefixWord ++ tailWord_364696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364734 : List Nat := [4, 2, 1, 1, 5, 6]
def baseStart_364734 : Nat := 118140960795 + 364734 * 2 ^ 59
def prefixEnd_364734 : Nat := 4983230072969 + 3 ^ 40 * 364734 * 2
def baseEnd_364734 : Nat := 12331447113552672279679

theorem tailTrace_364734 : CollatzResearch.WordTrace tailWord_364734 prefixEnd_364734 12331447113552672279679 := by
  unfold tailWord_364734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662867732579810556627657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8868627907092322968680837 1662867732579810556627657)
  ·
    refine ⟨1247150799434857917470743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1662867732579810556627657 1247150799434857917470743)
    ·
      refine ⟨1870726199152286876206115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247150799434857917470743 1870726199152286876206115)
      ·
        refine ⟨2806089298728430314309173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1870726199152286876206115 2806089298728430314309173)
        ·
          refine ⟨263070871755790341966485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2806089298728430314309173 263070871755790341966485)
          ·
            refine ⟨12331447113552672279679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 263070871755790341966485 12331447113552672279679)
            ·
              rfl

theorem cell19_364734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 6].length) (baseStart_364734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364734 prefixEnd_364734 := by exact prefixLift 364734
  have htrace : WordTrace (prefixWord ++ tailWord_364734) baseStart_364734 baseEnd_364734 := by
    simpa [prefixWord, tailWord_364734, baseEnd_364734] using wordTrace_append hprefix tailTrace_364734
  have hstable : (prefixWord ++ tailWord_364734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364734).length < 2 ^ (prefixWord ++ tailWord_364734).sum := by decide
  have hdescent : baseEnd_364734 < baseStart_364734 := by decide
  rcases family_descends (prefixWord ++ tailWord_364734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364829 : List Nat := [1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_364829 : Nat := 118140960795 + 364829 * 2 ^ 59
def prefixEnd_364829 : Nat := 4983230072969 + 3 ^ 40 * 364829 * 2
def baseEnd_364829 : Nat := 111011931081041978405741

theorem tailTrace_364829 : CollatzResearch.WordTrace tailWord_364829 prefixEnd_364829 111011931081041978405741 := by
  unfold tailWord_364829
  simp only [CollatzResearch.WordTrace]
  refine ⟨13306406795294315677729541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8870937863529543785153027 13306406795294315677729541)
  ·
    refine ⟨2494951274117684189574289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13306406795294315677729541 2494951274117684189574289)
    ·
      refine ⟨1871213455588263142180717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2494951274117684189574289 1871213455588263142180717)
      ·
        refine ⟨701705045845598678317769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1871213455588263142180717 701705045845598678317769)
        ·
          refine ⟨526278784384199008738327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701705045845598678317769 526278784384199008738327)
          ·
            refine ⟨789418176576298513107491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526278784384199008738327 789418176576298513107491)
            ·
              refine ⟨1184127264864447769661237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789418176576298513107491 1184127264864447769661237)
              ·
                refine ⟨111011931081041978405741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1184127264864447769661237 111011931081041978405741)
                ·
                  rfl

theorem cell19_364829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_364829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364829 prefixEnd_364829 := by exact prefixLift 364829
  have htrace : WordTrace (prefixWord ++ tailWord_364829) baseStart_364829 baseEnd_364829 := by
    simpa [prefixWord, tailWord_364829, baseEnd_364829] using wordTrace_append hprefix tailTrace_364829
  have hstable : (prefixWord ++ tailWord_364829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364829).length < 2 ^ (prefixWord ++ tailWord_364829).sum := by decide
  have hdescent : baseEnd_364829 < baseStart_364829 := by decide
  rcases family_descends (prefixWord ++ tailWord_364829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364831 : List Nat := [1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_364831 : Nat := 118140960795 + 364831 * 2 ^ 59
def prefixEnd_364831 : Nat := 4983230072969 + 3 ^ 40 * 364831 * 2
def baseEnd_364831 : Nat := 111012539650706566361291

theorem tailTrace_364831 : CollatzResearch.WordTrace tailWord_364831 prefixEnd_364831 111012539650706566361291 := by
  unfold tailWord_364831
  simp only [CollatzResearch.WordTrace]
  refine ⟨13306479741287070019302347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8870986494191380012868231 13306479741287070019302347)
  ·
    refine ⟨19959719611930605028953521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13306479741287070019302347 19959719611930605028953521)
    ·
      refine ⟨14969789708947953771715141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19959719611930605028953521 14969789708947953771715141)
      ·
        refine ⟨2806835570427741332196589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14969789708947953771715141 2806835570427741332196589)
        ·
          refine ⟨1052563338910402999573721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2806835570427741332196589 1052563338910402999573721)
          ·
            refine ⟨789422504182802249680291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052563338910402999573721 789422504182802249680291)
            ·
              refine ⟨1184133756274203374520437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789422504182802249680291 1184133756274203374520437)
              ·
                refine ⟨111012539650706566361291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1184133756274203374520437 111012539650706566361291)
                ·
                  rfl

theorem cell19_364831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_364831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364831 prefixEnd_364831 := by exact prefixLift 364831
  have htrace : WordTrace (prefixWord ++ tailWord_364831) baseStart_364831 baseEnd_364831 := by
    simpa [prefixWord, tailWord_364831, baseEnd_364831] using wordTrace_append hprefix tailTrace_364831
  have hstable : (prefixWord ++ tailWord_364831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364831).length < 2 ^ (prefixWord ++ tailWord_364831).sum := by decide
  have hdescent : baseEnd_364831 < baseStart_364831 := by decide
  rcases family_descends (prefixWord ++ tailWord_364831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364846 : List Nat := [4, 1, 3, 3, 1, 2, 5]
def baseStart_364846 : Nat := 118140960795 + 364846 * 2 ^ 59
def prefixEnd_364846 : Nat := 4983230072969 + 3 ^ 40 * 364846 * 2
def baseEnd_364846 : Nat := 37005701307730325342639

theorem tailTrace_364846 : CollatzResearch.WordTrace tailWord_364846 prefixEnd_364846 37005701307730325342639 := by
  unfold tailWord_364846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663378354529090947637299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8871351224155151720732261 1663378354529090947637299)
  ·
    refine ⟨2495067531793636421455949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1663378354529090947637299 2495067531793636421455949)
    ·
      refine ⟨935650324422613658045981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2495067531793636421455949 935650324422613658045981)
      ·
        refine ⟨350868871658480121767243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 935650324422613658045981 350868871658480121767243)
        ·
          refine ⟨526303307487720182650865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350868871658480121767243 526303307487720182650865)
          ·
            refine ⟨394727480615790136988149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526303307487720182650865 394727480615790136988149)
            ·
              refine ⟨37005701307730325342639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 394727480615790136988149 37005701307730325342639)
              ·
                rfl

theorem cell19_364846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_364846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364846 prefixEnd_364846 := by exact prefixLift 364846
  have htrace : WordTrace (prefixWord ++ tailWord_364846) baseStart_364846 baseEnd_364846 := by
    simpa [prefixWord, tailWord_364846, baseEnd_364846] using wordTrace_append hprefix tailTrace_364846
  have hstable : (prefixWord ++ tailWord_364846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364846).length < 2 ^ (prefixWord ++ tailWord_364846).sum := by decide
  have hdescent : baseEnd_364846 < baseStart_364846 := by decide
  rcases family_descends (prefixWord ++ tailWord_364846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364996 : List Nat := [2, 3, 3, 2, 3, 1, 2, 3]
def baseStart_364996 : Nat := 118140960795 + 364996 * 2 ^ 59
def prefixEnd_364996 : Nat := 4983230072969 + 3 ^ 40 * 364996 * 2
def baseEnd_364996 : Nat := 111062746648035072694175

theorem tailTrace_364996 : CollatzResearch.WordTrace tailWord_364996 prefixEnd_364996 111062746648035072694175 := by
  unfold tailWord_364996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6656248892844651599529421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8874998523792868799372561 6656248892844651599529421)
  ·
    refine ⟨2496093334816744349823533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6656248892844651599529421 2496093334816744349823533)
    ·
      refine ⟨936035000556279131183825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2496093334816744349823533 936035000556279131183825)
      ·
        refine ⟨702026250417209348387869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 936035000556279131183825 702026250417209348387869)
        ·
          refine ⟨263259843906453505645451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 702026250417209348387869 263259843906453505645451)
          ·
            refine ⟨394889765859680258468177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263259843906453505645451 394889765859680258468177)
            ·
              refine ⟨296167324394760193851133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394889765859680258468177 296167324394760193851133)
              ·
                refine ⟨111062746648035072694175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296167324394760193851133 111062746648035072694175)
                ·
                  rfl

theorem cell19_364996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_364996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_364996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_364996 prefixEnd_364996 := by exact prefixLift 364996
  have htrace : WordTrace (prefixWord ++ tailWord_364996) baseStart_364996 baseEnd_364996 := by
    simpa [prefixWord, tailWord_364996, baseEnd_364996] using wordTrace_append hprefix tailTrace_364996
  have hstable : (prefixWord ++ tailWord_364996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364996).length < 2 ^ (prefixWord ++ tailWord_364996).sum := by decide
  have hdescent : baseEnd_364996 < baseStart_364996 := by decide
  rcases family_descends (prefixWord ++ tailWord_364996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365000 : List Nat := [2, 1, 3, 1, 3, 4, 2, 3]
def baseStart_365000 : Nat := 118140960795 + 365000 * 2 ^ 59
def prefixEnd_365000 : Nat := 4983230072969 + 3 ^ 40 * 365000 * 2
def baseEnd_365000 : Nat := 111063963787364248605275

theorem tailTrace_365000 : CollatzResearch.WordTrace tailWord_365000 prefixEnd_365000 111063963787364248605275 := by
  unfold tailWord_365000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6656321838837405941102227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8875095785116541254802969 6656321838837405941102227)
  ·
    refine ⟨9984482758256108911653341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6656321838837405941102227 9984482758256108911653341)
    ·
      refine ⟨3744181034346040841870003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9984482758256108911653341 3744181034346040841870003)
      ·
        refine ⟨5616271551519061262805005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3744181034346040841870003 5616271551519061262805005)
        ·
          refine ⟨2106101831819647973551877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5616271551519061262805005 2106101831819647973551877)
          ·
            refine ⟨394894093466183995040977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2106101831819647973551877 394894093466183995040977)
            ·
              refine ⟨296170570099637996280733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394894093466183995040977 296170570099637996280733)
              ·
                refine ⟨111063963787364248605275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296170570099637996280733 111063963787364248605275)
                ·
                  rfl

theorem cell19_365000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_365000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365000 prefixEnd_365000 := by exact prefixLift 365000
  have htrace : WordTrace (prefixWord ++ tailWord_365000) baseStart_365000 baseEnd_365000 := by
    simpa [prefixWord, tailWord_365000, baseEnd_365000] using wordTrace_append hprefix tailTrace_365000
  have hstable : (prefixWord ++ tailWord_365000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365000).length < 2 ^ (prefixWord ++ tailWord_365000).sum := by decide
  have hdescent : baseEnd_365000 < baseStart_365000 := by decide
  rcases family_descends (prefixWord ++ tailWord_365000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365023 : List Nat := [1, 1, 2, 3, 3, 2, 7]
def baseStart_365023 : Nat := 118140960795 + 365023 * 2 ^ 59
def prefixEnd_365023 : Nat := 4983230072969 + 3 ^ 40 * 365023 * 2
def baseEnd_365023 : Nat := 37023654112835670031367

theorem tailTrace_365023 : CollatzResearch.WordTrace tailWord_365023 prefixEnd_365023 37023654112835670031367 := by
  unfold tailWord_365023
  simp only [CollatzResearch.WordTrace]
  refine ⟨13313482556591486810291723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8875655037727657873527815 13313482556591486810291723)
  ·
    refine ⟨19970223834887230215437585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13313482556591486810291723 19970223834887230215437585)
    ·
      refine ⟨14977667876165422661578189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19970223834887230215437585 14977667876165422661578189)
      ·
        refine ⟨5616625453562033498091821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14977667876165422661578189 5616625453562033498091821)
        ·
          refine ⟨2106234545085762561784433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5616625453562033498091821 2106234545085762561784433)
          ·
            refine ⟨1579675908814321921338325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2106234545085762561784433 1579675908814321921338325)
            ·
              refine ⟨37023654112835670031367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1579675908814321921338325 37023654112835670031367)
              ·
                rfl

theorem cell19_365023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_365023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365023 prefixEnd_365023 := by exact prefixLift 365023
  have htrace : WordTrace (prefixWord ++ tailWord_365023) baseStart_365023 baseEnd_365023 := by
    simpa [prefixWord, tailWord_365023, baseEnd_365023] using wordTrace_append hprefix tailTrace_365023
  have hstable : (prefixWord ++ tailWord_365023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365023).length < 2 ^ (prefixWord ++ tailWord_365023).sum := by decide
  have hdescent : baseEnd_365023 < baseStart_365023 := by decide
  rcases family_descends (prefixWord ++ tailWord_365023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365061 : List Nat := [1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_365061 : Nat := 118140960795 + 365061 * 2 ^ 59
def prefixEnd_365061 : Nat := 4983230072969 + 3 ^ 40 * 365061 * 2
def baseEnd_365061 : Nat := 111082525162134181249553

theorem tailTrace_365061 : CollatzResearch.WordTrace tailWord_365061 prefixEnd_365061 111082525162134181249553 := by
  unfold tailWord_365061
  simp only [CollatzResearch.WordTrace]
  refine ⟨13314868530453819300175037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8876579020302546200116691 13314868530453819300175037)
  ·
    refine ⟨4993075698920182237565639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13314868530453819300175037 4993075698920182237565639)
    ·
      refine ⟨7489613548380273356348459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4993075698920182237565639 7489613548380273356348459)
      ·
        refine ⟨11234420322570410034522689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7489613548380273356348459 11234420322570410034522689)
        ·
          refine ⟨8425815241927807525892017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11234420322570410034522689 8425815241927807525892017)
          ·
            refine ⟨6319361431445855644419013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8425815241927807525892017 6319361431445855644419013)
            ·
              refine ⟨1184880268396097933328565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6319361431445855644419013 1184880268396097933328565)
              ·
                refine ⟨111082525162134181249553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1184880268396097933328565 111082525162134181249553)
                ·
                  rfl

theorem cell19_365061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_365061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365061 prefixEnd_365061 := by exact prefixLift 365061
  have htrace : WordTrace (prefixWord ++ tailWord_365061) baseStart_365061 baseEnd_365061 := by
    simpa [prefixWord, tailWord_365061, baseEnd_365061] using wordTrace_append hprefix tailTrace_365061
  have hstable : (prefixWord ++ tailWord_365061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365061).length < 2 ^ (prefixWord ++ tailWord_365061).sum := by decide
  have hdescent : baseEnd_365061 < baseStart_365061 := by decide
  rcases family_descends (prefixWord ++ tailWord_365061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365080 : List Nat := [2, 1, 2, 3, 3, 8]
def baseStart_365080 : Nat := 118140960795 + 365080 * 2 ^ 59
def prefixEnd_365080 : Nat := 4983230072969 + 3 ^ 40 * 365080 * 2
def baseEnd_365080 : Nat := 12343145174883085203031

theorem tailTrace_365080 : CollatzResearch.WordTrace tailWord_365080 prefixEnd_365080 12343145174883085203031 := by
  unfold tailWord_365080
  simp only [CollatzResearch.WordTrace]
  refine ⟨6657780758692492772558347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8877041011589990363411129 6657780758692492772558347)
  ·
    refine ⟨9986671138038739158837521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6657780758692492772558347 9986671138038739158837521)
    ·
      refine ⟨7490003353529054369128141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9986671138038739158837521 7490003353529054369128141)
      ·
        refine ⟨2808751257573395388423053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7490003353529054369128141 2808751257573395388423053)
        ·
          refine ⟨1053281721590023270658645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2808751257573395388423053 1053281721590023270658645)
          ·
            refine ⟨12343145174883085203031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1053281721590023270658645 12343145174883085203031)
            ·
              rfl

theorem cell19_365080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 8].length) (baseStart_365080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365080 prefixEnd_365080 := by exact prefixLift 365080
  have htrace : WordTrace (prefixWord ++ tailWord_365080) baseStart_365080 baseEnd_365080 := by
    simpa [prefixWord, tailWord_365080, baseEnd_365080] using wordTrace_append hprefix tailTrace_365080
  have hstable : (prefixWord ++ tailWord_365080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365080).length < 2 ^ (prefixWord ++ tailWord_365080).sum := by decide
  have hdescent : baseEnd_365080 < baseStart_365080 := by decide
  rcases family_descends (prefixWord ++ tailWord_365080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365137 : List Nat := [1, 2, 2, 1, 3, 4, 6]
def baseStart_365137 : Nat := 118140960795 + 365137 * 2 ^ 59
def prefixEnd_365137 : Nat := 4983230072969 + 3 ^ 40 * 365137 * 2
def baseEnd_365137 : Nat := 37035216936462841186819

theorem tailTrace_365137 : CollatzResearch.WordTrace tailWord_365137 prefixEnd_365137 37035216936462841186819 := by
  unfold tailWord_365137
  simp only [CollatzResearch.WordTrace]
  refine ⟨13317640478178484279941665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8878426985452322853294443 13317640478178484279941665)
  ·
    refine ⟨9988230358633863209956249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13317640478178484279941665 9988230358633863209956249)
    ·
      refine ⟨7491172768975397407467187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9988230358633863209956249 7491172768975397407467187)
      ·
        refine ⟨11236759153463096111200781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7491172768975397407467187 11236759153463096111200781)
        ·
          refine ⟨4213784682548661041700293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11236759153463096111200781 4213784682548661041700293)
          ·
            refine ⟨790084627977873945318805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4213784682548661041700293 790084627977873945318805)
            ·
              refine ⟨37035216936462841186819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 790084627977873945318805 37035216936462841186819)
              ·
                rfl

theorem cell19_365137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_365137 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365137 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365137 prefixEnd_365137 := by exact prefixLift 365137
  have htrace : WordTrace (prefixWord ++ tailWord_365137) baseStart_365137 baseEnd_365137 := by
    simpa [prefixWord, tailWord_365137, baseEnd_365137] using wordTrace_append hprefix tailTrace_365137
  have hstable : (prefixWord ++ tailWord_365137).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365137).length < 2 ^ (prefixWord ++ tailWord_365137).sum := by decide
  have hdescent : baseEnd_365137 < baseStart_365137 := by decide
  rcases family_descends (prefixWord ++ tailWord_365137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365156 : List Nat := [2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_365156 : Nat := 118140960795 + 365156 * 2 ^ 59
def prefixEnd_365156 : Nat := 4983230072969 + 3 ^ 40 * 365156 * 2
def baseEnd_365156 : Nat := 111111432221202109138183

theorem tailTrace_365156 : CollatzResearch.WordTrace tailWord_365156 prefixEnd_365156 111111432221202109138183 := by
  unfold tailWord_365156
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659166732554825262441661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8878888976739767016588881 6659166732554825262441661)
  ·
    refine ⟨2497187524708059473415623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6659166732554825262441661 2497187524708059473415623)
    ·
      refine ⟨3745781287062089210123435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2497187524708059473415623 3745781287062089210123435)
      ·
        refine ⟨5618671930593133815185153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3745781287062089210123435 5618671930593133815185153)
        ·
          refine ⟨4214003947944850361388865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5618671930593133815185153 4214003947944850361388865)
          ·
            refine ⟨3160502960958637771041649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4214003947944850361388865 3160502960958637771041649)
            ·
              refine ⟨2370377220718978328281237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160502960958637771041649 2370377220718978328281237)
              ·
                refine ⟨111111432221202109138183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2370377220718978328281237 111111432221202109138183)
                ·
                  rfl

theorem cell19_365156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_365156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365156 prefixEnd_365156 := by exact prefixLift 365156
  have htrace : WordTrace (prefixWord ++ tailWord_365156) baseStart_365156 baseEnd_365156 := by
    simpa [prefixWord, tailWord_365156, baseEnd_365156] using wordTrace_append hprefix tailTrace_365156
  have hstable : (prefixWord ++ tailWord_365156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365156).length < 2 ^ (prefixWord ++ tailWord_365156).sum := by decide
  have hdescent : baseEnd_365156 < baseStart_365156 := by decide
  rcases family_descends (prefixWord ++ tailWord_365156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365186 : List Nat := [3, 4, 3, 1, 1, 2, 5]
def baseStart_365186 : Nat := 118140960795 + 365186 * 2 ^ 59
def prefixEnd_365186 : Nat := 4983230072969 + 3 ^ 40 * 365186 * 2
def baseEnd_365186 : Nat := 37040186922056976157145

theorem tailTrace_365186 : CollatzResearch.WordTrace tailWord_365186 prefixEnd_365186 37040186922056976157145 := by
  unfold tailWord_365186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329856913750241412118853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8879618436667310432316941 3329856913750241412118853)
  ·
    refine ⟨624348171328170264772285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3329856913750241412118853 624348171328170264772285)
    ·
      refine ⟨234130564248063849289607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 624348171328170264772285 234130564248063849289607)
      ·
        refine ⟨351195846372095773934411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234130564248063849289607 351195846372095773934411)
        ·
          refine ⟨526793769558143660901617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351195846372095773934411 526793769558143660901617)
          ·
            refine ⟨395095327168607745676213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526793769558143660901617 395095327168607745676213)
            ·
              refine ⟨37040186922056976157145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 395095327168607745676213 37040186922056976157145)
              ·
                rfl

theorem cell19_365186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 5].length) (baseStart_365186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365186 prefixEnd_365186 := by exact prefixLift 365186
  have htrace : WordTrace (prefixWord ++ tailWord_365186) baseStart_365186 baseEnd_365186 := by
    simpa [prefixWord, tailWord_365186, baseEnd_365186] using wordTrace_append hprefix tailTrace_365186
  have hstable : (prefixWord ++ tailWord_365186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365186).length < 2 ^ (prefixWord ++ tailWord_365186).sum := by decide
  have hdescent : baseEnd_365186 < baseStart_365186 := by decide
  rcases family_descends (prefixWord ++ tailWord_365186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365213 : List Nat := [1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_365213 : Nat := 118140960795 + 365213 * 2 ^ 59
def prefixEnd_365213 : Nat := 4983230072969 + 3 ^ 40 * 365213 * 2
def baseEnd_365213 : Nat := 111128776456642865871361

theorem tailTrace_365213 : CollatzResearch.WordTrace tailWord_365213 prefixEnd_365213 111128776456642865871361 := by
  unfold tailWord_365213
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320412425903149259708293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8880274950602099506472195 13320412425903149259708293)
  ·
    refine ⟨2497577329856840486195305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13320412425903149259708293 2497577329856840486195305)
    ·
      refine ⟨1873182997392630364646479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2497577329856840486195305 1873182997392630364646479)
      ·
        refine ⟨2809774496088945546969719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873182997392630364646479 2809774496088945546969719)
        ·
          refine ⟨4214661744133418320454579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809774496088945546969719 4214661744133418320454579)
          ·
            refine ⟨6321992616200127480681869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214661744133418320454579 6321992616200127480681869)
            ·
              refine ⟨2370747231075047805255701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6321992616200127480681869 2370747231075047805255701)
              ·
                refine ⟨111128776456642865871361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2370747231075047805255701 111128776456642865871361)
                ·
                  rfl

theorem cell19_365213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_365213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365213 prefixEnd_365213 := by exact prefixLift 365213
  have htrace : WordTrace (prefixWord ++ tailWord_365213) baseStart_365213 baseEnd_365213 := by
    simpa [prefixWord, tailWord_365213, baseEnd_365213] using wordTrace_append hprefix tailTrace_365213
  have hstable : (prefixWord ++ tailWord_365213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365213).length < 2 ^ (prefixWord ++ tailWord_365213).sum := by decide
  have hdescent : baseEnd_365213 < baseStart_365213 := by decide
  rcases family_descends (prefixWord ++ tailWord_365213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365249 : List Nat := [1, 2, 6, 2, 8]
def baseStart_365249 : Nat := 118140960795 + 365249 * 2 ^ 59
def prefixEnd_365249 : Nat := 4983230072969 + 3 ^ 40 * 365249 * 2
def baseEnd_365249 : Nat := 4116286322615016632269

theorem tailTrace_365249 : CollatzResearch.WordTrace tailWord_365249 prefixEnd_365249 4116286322615016632269 := by
  unfold tailWord_365249
  simp only [CollatzResearch.WordTrace]
  refine ⟨13321725453772727408018801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8881150302515151605345867 13321725453772727408018801)
  ·
    refine ⟨9991294090329545556014101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13321725453772727408018801 9991294090329545556014101)
    ·
      refine ⟨468341910484197447938161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9991294090329545556014101 468341910484197447938161)
      ·
        refine ⟨351256432863148085953621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468341910484197447938161 351256432863148085953621)
        ·
          refine ⟨4116286322615016632269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 351256432863148085953621 4116286322615016632269)
          ·
            rfl

theorem cell19_365249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 8].length) (baseStart_365249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365249 prefixEnd_365249 := by exact prefixLift 365249
  have htrace : WordTrace (prefixWord ++ tailWord_365249) baseStart_365249 baseEnd_365249 := by
    simpa [prefixWord, tailWord_365249, baseEnd_365249] using wordTrace_append hprefix tailTrace_365249
  have hstable : (prefixWord ++ tailWord_365249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365249).length < 2 ^ (prefixWord ++ tailWord_365249).sum := by decide
  have hdescent : baseEnd_365249 < baseStart_365249 := by decide
  rcases family_descends (prefixWord ++ tailWord_365249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365266 : List Nat := [3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_365266 : Nat := 118140960795 + 365266 * 2 ^ 59
def prefixEnd_365266 : Nat := 4983230072969 + 3 ^ 40 * 365266 * 2
def baseEnd_365266 : Nat := 111144903552754446693439

theorem tailTrace_365266 : CollatzResearch.WordTrace tailWord_365266 prefixEnd_365266 111144903552754446693439 := by
  unfold tailWord_365266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330586373677784827846913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8881563663140759540925101 3330586373677784827846913)
  ·
    refine ⟨2497939780258338620885185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3330586373677784827846913 2497939780258338620885185)
    ·
      refine ⟨1873454835193753965663889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2497939780258338620885185 1873454835193753965663889)
      ·
        refine ⟨1405091126395315474247917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1873454835193753965663889 1405091126395315474247917)
        ·
          refine ⟨526909172398243302842969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1405091126395315474247917 526909172398243302842969)
          ·
            refine ⟨395181879298682477132227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526909172398243302842969 395181879298682477132227)
            ·
              refine ⟨592772818948023715698341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395181879298682477132227 592772818948023715698341)
              ·
                refine ⟨111144903552754446693439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592772818948023715698341 111144903552754446693439)
                ·
                  rfl

theorem cell19_365266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_365266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365266 prefixEnd_365266 := by exact prefixLift 365266
  have htrace : WordTrace (prefixWord ++ tailWord_365266) baseStart_365266 baseEnd_365266 := by
    simpa [prefixWord, tailWord_365266, baseEnd_365266] using wordTrace_append hprefix tailTrace_365266
  have hstable : (prefixWord ++ tailWord_365266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365266).length < 2 ^ (prefixWord ++ tailWord_365266).sum := by decide
  have hdescent : baseEnd_365266 < baseStart_365266 := by decide
  rcases family_descends (prefixWord ++ tailWord_365266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365308 : List Nat := [2, 2, 2, 1, 3, 3, 6]
def baseStart_365308 : Nat := 118140960795 + 365308 * 2 ^ 59
def prefixEnd_365308 : Nat := 4983230072969 + 3 ^ 40 * 365308 * 2
def baseEnd_365308 : Nat := 37052561171903597919997

theorem tailTrace_365308 : CollatzResearch.WordTrace tailWord_365308 prefixEnd_365308 37052561171903597919997 := by
  unfold tailWord_365308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6661938680279490242208289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8882584907039320322944385 6661938680279490242208289)
  ·
    refine ⟨4996454010209617681656217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6661938680279490242208289 4996454010209617681656217)
    ·
      refine ⟨3747340507657213261242163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4996454010209617681656217 3747340507657213261242163)
      ·
        refine ⟨5621010761485819891863245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747340507657213261242163 5621010761485819891863245)
        ·
          refine ⟨2107879035557182459448717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5621010761485819891863245 2107879035557182459448717)
          ·
            refine ⟨790454638333943422293269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2107879035557182459448717 790454638333943422293269)
            ·
              refine ⟨37052561171903597919997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 790454638333943422293269 37052561171903597919997)
              ·
                rfl

theorem cell19_365308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_365308 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365308 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365308 prefixEnd_365308 := by exact prefixLift 365308
  have htrace : WordTrace (prefixWord ++ tailWord_365308) baseStart_365308 baseEnd_365308 := by
    simpa [prefixWord, tailWord_365308, baseEnd_365308] using wordTrace_append hprefix tailTrace_365308
  have hstable : (prefixWord ++ tailWord_365308).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365308).length < 2 ^ (prefixWord ++ tailWord_365308).sum := by decide
  have hdescent : baseEnd_365308 < baseStart_365308 := by decide
  rcases family_descends (prefixWord ++ tailWord_365308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365344 : List Nat := [2, 1, 1, 5, 1, 2, 4, 3]
def baseStart_365344 : Nat := 118140960795 + 365344 * 2 ^ 59
def prefixEnd_365344 : Nat := 4983230072969 + 3 ^ 40 * 365344 * 2
def baseEnd_365344 : Nat := 111168637769673376959893

theorem tailTrace_365344 : CollatzResearch.WordTrace tailWord_365344 prefixEnd_365344 111168637769673376959893 := by
  unfold tailWord_365344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6662595194214279316363543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8883460258952372421818057 6662595194214279316363543)
  ·
    refine ⟨9993892791321418974545315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6662595194214279316363543 9993892791321418974545315)
    ·
      refine ⟨14990839186982128461817973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9993892791321418974545315 14990839186982128461817973)
      ·
        refine ⟨1405391173779574543295435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14990839186982128461817973 1405391173779574543295435)
        ·
          refine ⟨2108086760669361814943153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405391173779574543295435 2108086760669361814943153)
          ·
            refine ⟨1581065070502021361207365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2108086760669361814943153 1581065070502021361207365)
            ·
              refine ⟨296449700719129005226381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1581065070502021361207365 296449700719129005226381)
              ·
                refine ⟨111168637769673376959893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296449700719129005226381 111168637769673376959893)
                ·
                  rfl

theorem cell19_365344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_365344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365344 prefixEnd_365344 := by exact prefixLift 365344
  have htrace : WordTrace (prefixWord ++ tailWord_365344) baseStart_365344 baseEnd_365344 := by
    simpa [prefixWord, tailWord_365344, baseEnd_365344] using wordTrace_append hprefix tailTrace_365344
  have hstable : (prefixWord ++ tailWord_365344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365344).length < 2 ^ (prefixWord ++ tailWord_365344).sum := by decide
  have hdescent : baseEnd_365344 < baseStart_365344 := by decide
  rcases family_descends (prefixWord ++ tailWord_365344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365365 : List Nat := [1, 3, 3, 1, 3, 1, 7]
def baseStart_365365 : Nat := 118140960795 + 365365 * 2 ^ 59
def prefixEnd_365365 : Nat := 4983230072969 + 3 ^ 40 * 365365 * 2
def baseEnd_365365 : Nat := 37058342583717183497723

theorem tailTrace_365365 : CollatzResearch.WordTrace tailWord_365365 prefixEnd_365365 37058342583717183497723 := by
  unfold tailWord_365365
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325956321352479219241549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8883970880901652812827699 13325956321352479219241549)
  ·
    refine ⟨4997233620507179707215581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13325956321352479219241549 4997233620507179707215581)
    ·
      refine ⟨1873962607690192390205843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4997233620507179707215581 1873962607690192390205843)
      ·
        refine ⟨2810943911535288585308765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873962607690192390205843 2810943911535288585308765)
        ·
          refine ⟨1054103966825733219490787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2810943911535288585308765 1054103966825733219490787)
          ·
            refine ⟨1581155950238599829236181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054103966825733219490787 1581155950238599829236181)
            ·
              refine ⟨37058342583717183497723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1581155950238599829236181 37058342583717183497723)
              ·
                rfl

theorem cell19_365365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_365365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365365 prefixEnd_365365 := by exact prefixLift 365365
  have htrace : WordTrace (prefixWord ++ tailWord_365365) baseStart_365365 baseEnd_365365 := by
    simpa [prefixWord, tailWord_365365, baseEnd_365365] using wordTrace_append hprefix tailTrace_365365
  have hstable : (prefixWord ++ tailWord_365365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365365).length < 2 ^ (prefixWord ++ tailWord_365365).sum := by decide
  have hdescent : baseEnd_365365 < baseStart_365365 := by decide
  rcases family_descends (prefixWord ++ tailWord_365365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365384 : List Nat := [2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_365384 : Nat := 118140960795 + 365384 * 2 ^ 59
def prefixEnd_365384 : Nat := 4983230072969 + 3 ^ 40 * 365384 * 2
def baseEnd_365384 : Nat := 111180809162965136070895

theorem tailTrace_365384 : CollatzResearch.WordTrace tailWord_365384 prefixEnd_365384 111180809162965136070895 := by
  unfold tailWord_365384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663324654141822732091603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8884432872189096976122137 6663324654141822732091603)
  ·
    refine ⟨9994986981212734098137405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6663324654141822732091603 9994986981212734098137405)
    ·
      refine ⟨3748120117954775286801527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9994986981212734098137405 3748120117954775286801527)
      ·
        refine ⟨5622180176932162930202291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3748120117954775286801527 5622180176932162930202291)
        ·
          refine ⟨8433270265398244395303437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622180176932162930202291 8433270265398244395303437)
          ·
            refine ⟨3162476349524341648238789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8433270265398244395303437 3162476349524341648238789)
            ·
              refine ⟨592964315535814059044773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3162476349524341648238789 592964315535814059044773)
              ·
                refine ⟨111180809162965136070895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592964315535814059044773 111180809162965136070895)
                ·
                  rfl

theorem cell19_365384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_365384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365384 prefixEnd_365384 := by exact prefixLift 365384
  have htrace : WordTrace (prefixWord ++ tailWord_365384) baseStart_365384 baseEnd_365384 := by
    simpa [prefixWord, tailWord_365384, baseEnd_365384] using wordTrace_append hprefix tailTrace_365384
  have hstable : (prefixWord ++ tailWord_365384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365384).length < 2 ^ (prefixWord ++ tailWord_365384).sum := by decide
  have hdescent : baseEnd_365384 < baseStart_365384 := by decide
  rcases family_descends (prefixWord ++ tailWord_365384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365422 : List Nat := [4, 1, 2, 3, 9]
def baseStart_365422 : Nat := 118140960795 + 365422 * 2 ^ 59
def prefixEnd_365422 : Nat := 4983230072969 + 3 ^ 40 * 365422 * 2
def baseEnd_365422 : Nat := 4118235999503418786161

theorem tailTrace_365422 : CollatzResearch.WordTrace tailWord_365422 prefixEnd_365422 4118235999503418786161 := by
  unfold tailWord_365422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666004410268247244258315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8885356854763985302711013 1666004410268247244258315)
  ·
    refine ⟨2499006615402370866387473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1666004410268247244258315 2499006615402370866387473)
    ·
      refine ⟨1874254961551778149790605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2499006615402370866387473 1874254961551778149790605)
      ·
        refine ⟨702845610581916806171477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1874254961551778149790605 702845610581916806171477)
        ·
          refine ⟨4118235999503418786161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 702845610581916806171477 4118235999503418786161)
          ·
            rfl

theorem cell19_365422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 9].length) (baseStart_365422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365422 prefixEnd_365422 := by exact prefixLift 365422
  have htrace : WordTrace (prefixWord ++ tailWord_365422) baseStart_365422 baseEnd_365422 := by
    simpa [prefixWord, tailWord_365422, baseEnd_365422] using wordTrace_append hprefix tailTrace_365422
  have hstable : (prefixWord ++ tailWord_365422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365422).length < 2 ^ (prefixWord ++ tailWord_365422).sum := by decide
  have hdescent : baseEnd_365422 < baseStart_365422 := by decide
  rcases family_descends (prefixWord ++ tailWord_365422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365481 : List Nat := [1, 2, 1, 1, 1, 1, 12]
def baseStart_365481 : Nat := 118140960795 + 365481 * 2 ^ 59
def prefixEnd_365481 : Nat := 4983230072969 + 3 ^ 40 * 365481 * 2
def baseEnd_365481 : Nat := 37070108263899217305025

theorem tailTrace_365481 : CollatzResearch.WordTrace tailWord_365481 prefixEnd_365481 37070108263899217305025 := by
  unfold tailWord_365481
  simp only [CollatzResearch.WordTrace]
  refine ⟨13330187188932231030464297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8886791459288154020309531 13330187188932231030464297)
  ·
    refine ⟨9997640391699173272848223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13330187188932231030464297 9997640391699173272848223)
    ·
      refine ⟨14996460587548759909272335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9997640391699173272848223 14996460587548759909272335)
      ·
        refine ⟨22494690881323139863908503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14996460587548759909272335 22494690881323139863908503)
        ·
          refine ⟨33742036321984709795862755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22494690881323139863908503 33742036321984709795862755)
          ·
            refine ⟨50613054482977064693794133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33742036321984709795862755 50613054482977064693794133)
            ·
              refine ⟨37070108263899217305025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 50613054482977064693794133 37070108263899217305025)
              ·
                rfl

theorem cell19_365481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_365481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365481 prefixEnd_365481 := by exact prefixLift 365481
  have htrace : WordTrace (prefixWord ++ tailWord_365481) baseStart_365481 baseEnd_365481 := by
    simpa [prefixWord, tailWord_365481, baseEnd_365481] using wordTrace_append hprefix tailTrace_365481
  have hstable : (prefixWord ++ tailWord_365481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365481).length < 2 ^ (prefixWord ++ tailWord_365481).sum := by decide
  have hdescent : baseEnd_365481 < baseStart_365481 := by decide
  rcases family_descends (prefixWord ++ tailWord_365481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365515 : List Nat := [1, 1, 1, 1, 3, 7, 2, 3]
def baseStart_365515 : Nat := 118140960795 + 365515 * 2 ^ 59
def prefixEnd_365515 : Nat := 4983230072969 + 3 ^ 40 * 365515 * 2
def baseEnd_365515 : Nat := 111220670475995647159427

theorem tailTrace_365515 : CollatzResearch.WordTrace tailWord_365515 prefixEnd_365515 111220670475995647159427 := by
  unfold tailWord_365515
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331427270809054837201999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8887618180539369891467999 13331427270809054837201999)
  ·
    refine ⟨19997140906213582255802999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13331427270809054837201999 19997140906213582255802999)
    ·
      refine ⟨29995711359320373383704499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19997140906213582255802999 29995711359320373383704499)
      ·
        refine ⟨44993567038980560075556749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29995711359320373383704499 44993567038980560075556749)
        ·
          refine ⟨16872587639617710028333781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44993567038980560075556749 16872587639617710028333781)
          ·
            refine ⟨395451272803540078789073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16872587639617710028333781 395451272803540078789073)
            ·
              refine ⟨296588454602655059091805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395451272803540078789073 296588454602655059091805)
              ·
                refine ⟨111220670475995647159427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296588454602655059091805 111220670475995647159427)
                ·
                  rfl

theorem cell19_365515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_365515 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365515 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365515 prefixEnd_365515 := by exact prefixLift 365515
  have htrace : WordTrace (prefixWord ++ tailWord_365515) baseStart_365515 baseEnd_365515 := by
    simpa [prefixWord, tailWord_365515, baseEnd_365515] using wordTrace_append hprefix tailTrace_365515
  have hstable : (prefixWord ++ tailWord_365515).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365515).length < 2 ^ (prefixWord ++ tailWord_365515).sum := by decide
  have hdescent : baseEnd_365515 < baseStart_365515 := by decide
  rcases family_descends (prefixWord ++ tailWord_365515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365629 : List Nat := [1, 4, 1, 3, 1, 3, 3, 3]
def baseStart_365629 : Nat := 118140960795 + 365629 * 2 ^ 59
def prefixEnd_365629 : Nat := 4983230072969 + 3 ^ 40 * 365629 * 2
def baseEnd_365629 : Nat := 111255358946877160625783

theorem tailTrace_365629 : CollatzResearch.WordTrace tailWord_365629 prefixEnd_365629 111255358946877160625783 := by
  unfold tailWord_365629
  simp only [CollatzResearch.WordTrace]
  refine ⟨13335585192396052306851941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8890390128264034871234627 13335585192396052306851941)
  ·
    refine ⟨2500422223574259807534739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13335585192396052306851941 2500422223574259807534739)
    ·
      refine ⟨3750633335361389711302109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2500422223574259807534739 3750633335361389711302109)
      ·
        refine ⟨1406487500760521141738291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3750633335361389711302109 1406487500760521141738291)
        ·
          refine ⟨2109731251140781712607437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406487500760521141738291 2109731251140781712607437)
          ·
            refine ⟨791149219177793142227789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2109731251140781712607437 791149219177793142227789)
            ·
              refine ⟨296680957191672428335421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 791149219177793142227789 296680957191672428335421)
              ·
                refine ⟨111255358946877160625783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296680957191672428335421 111255358946877160625783)
                ·
                  rfl

theorem cell19_365629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_365629 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365629 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365629 prefixEnd_365629 := by exact prefixLift 365629
  have htrace : WordTrace (prefixWord ++ tailWord_365629) baseStart_365629 baseEnd_365629 := by
    simpa [prefixWord, tailWord_365629, baseEnd_365629] using wordTrace_append hprefix tailTrace_365629
  have hstable : (prefixWord ++ tailWord_365629).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365629).length < 2 ^ (prefixWord ++ tailWord_365629).sum := by decide
  have hdescent : baseEnd_365629 < baseStart_365629 := by decide
  rcases family_descends (prefixWord ++ tailWord_365629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365650 : List Nat := [3, 2, 2, 1, 3, 2, 6]
def baseStart_365650 : Nat := 118140960795 + 365650 * 2 ^ 59
def prefixEnd_365650 : Nat := 4983230072969 + 3 ^ 40 * 365650 * 2
def baseEnd_365650 : Nat := 37087249642785111386353

theorem tailTrace_365650 : CollatzResearch.WordTrace tailWord_365650 prefixEnd_365650 37087249642785111386353 := by
  unfold tailWord_365650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334087781329993223341601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8890900750213315262244269 3334087781329993223341601)
  ·
    refine ⟨2500565835997494917506201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3334087781329993223341601 2500565835997494917506201)
    ·
      refine ⟨1875424376998121188129651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2500565835997494917506201 1875424376998121188129651)
      ·
        refine ⟨2813136565497181782194477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875424376998121188129651 2813136565497181782194477)
        ·
          refine ⟨1054926212061443168322929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2813136565497181782194477 1054926212061443168322929)
          ·
            refine ⟨791194659046082376242197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054926212061443168322929 791194659046082376242197)
            ·
              refine ⟨37087249642785111386353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 791194659046082376242197 37087249642785111386353)
              ·
                rfl

theorem cell19_365650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_365650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365650 prefixEnd_365650 := by exact prefixLift 365650
  have htrace : WordTrace (prefixWord ++ tailWord_365650) baseStart_365650 baseEnd_365650 := by
    simpa [prefixWord, tailWord_365650, baseEnd_365650] using wordTrace_append hprefix tailTrace_365650
  have hstable : (prefixWord ++ tailWord_365650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365650).length < 2 ^ (prefixWord ++ tailWord_365650).sum := by decide
  have hdescent : baseEnd_365650 < baseStart_365650 := by decide
  rcases family_descends (prefixWord ++ tailWord_365650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365688 : List Nat := [2, 1, 2, 1, 1, 1, 8, 3]
def baseStart_365688 : Nat := 118140960795 + 365688 * 2 ^ 59
def prefixEnd_365688 : Nat := 4983230072969 + 3 ^ 40 * 365688 * 2
def baseEnd_365688 : Nat := 111273311751982505314511

theorem tailTrace_365688 : CollatzResearch.WordTrace tailWord_365688 prefixEnd_365688 111273311751982505314511 := by
  unfold tailWord_365688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668868549591152691624859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8891824732788203588833145 6668868549591152691624859)
  ·
    refine ⟨10003302824386729037437289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6668868549591152691624859 10003302824386729037437289)
    ·
      refine ⟨7502477118290046778077967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10003302824386729037437289 7502477118290046778077967)
      ·
        refine ⟨11253715677435070167116951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7502477118290046778077967 11253715677435070167116951)
        ·
          refine ⟨16880573516152605250675427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11253715677435070167116951 16880573516152605250675427)
          ·
            refine ⟨25320860274228907876013141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16880573516152605250675427 25320860274228907876013141)
            ·
              refine ⟨296728831338620014172029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 25320860274228907876013141 296728831338620014172029)
              ·
                refine ⟨111273311751982505314511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296728831338620014172029 111273311751982505314511)
                ·
                  rfl

theorem cell19_365688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_365688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365688 prefixEnd_365688 := by exact prefixLift 365688
  have htrace : WordTrace (prefixWord ++ tailWord_365688) baseStart_365688 baseEnd_365688 := by
    simpa [prefixWord, tailWord_365688, baseEnd_365688] using wordTrace_append hprefix tailTrace_365688
  have hstable : (prefixWord ++ tailWord_365688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365688).length < 2 ^ (prefixWord ++ tailWord_365688).sum := by decide
  have hdescent : baseEnd_365688 < baseStart_365688 := by decide
  rcases family_descends (prefixWord ++ tailWord_365688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365745 : List Nat := [1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_365745 : Nat := 118140960795 + 365745 * 2 ^ 59
def prefixEnd_365745 : Nat := 4983230072969 + 3 ^ 40 * 365745 * 2
def baseEnd_365745 : Nat := 111290655987423262047689

theorem tailTrace_365745 : CollatzResearch.WordTrace tailWord_365745 prefixEnd_365745 111290655987423262047689 := by
  unfold tailWord_365745
  simp only [CollatzResearch.WordTrace]
  refine ⟨13339816059975804118074689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8893210706650536078716459 13339816059975804118074689)
  ·
    refine ⟨10004862044981853088556017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13339816059975804118074689 10004862044981853088556017)
    ·
      refine ⟨7503646533736389816417013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10004862044981853088556017 7503646533736389816417013)
      ·
        refine ⟨703466862537786545289095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7503646533736389816417013 703466862537786545289095)
        ·
          refine ⟨1055200293806679817933643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703466862537786545289095 1055200293806679817933643)
          ·
            refine ⟨1582800440710019726900465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055200293806679817933643 1582800440710019726900465)
            ·
              refine ⟨1187100330532514795175349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582800440710019726900465 1187100330532514795175349)
              ·
                refine ⟨111290655987423262047689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1187100330532514795175349 111290655987423262047689)
                ·
                  rfl

theorem cell19_365745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_365745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365745 prefixEnd_365745 := by exact prefixLift 365745
  have htrace : WordTrace (prefixWord ++ tailWord_365745) baseStart_365745 baseEnd_365745 := by
    simpa [prefixWord, tailWord_365745, baseEnd_365745] using wordTrace_append hprefix tailTrace_365745
  have hstable : (prefixWord ++ tailWord_365745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365745).length < 2 ^ (prefixWord ++ tailWord_365745).sum := by decide
  have hdescent : baseEnd_365745 < baseStart_365745 := by decide
  rcases family_descends (prefixWord ++ tailWord_365745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365747 : List Nat := [1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_365747 : Nat := 118140960795 + 365747 * 2 ^ 59
def prefixEnd_365747 : Nat := 4983230072969 + 3 ^ 40 * 365747 * 2
def baseEnd_365747 : Nat := 111291264557087850003239

theorem tailTrace_365747 : CollatzResearch.WordTrace tailWord_365747 prefixEnd_365747 111291264557087850003239 := by
  unfold tailWord_365747
  simp only [CollatzResearch.WordTrace]
  refine ⟨13339889005968558459647495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8893259337312372306431663 13339889005968558459647495)
  ·
    refine ⟨20009833508952837689471243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13339889005968558459647495 20009833508952837689471243)
    ·
      refine ⟨30014750263429256534206865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20009833508952837689471243 30014750263429256534206865)
      ·
        refine ⟨22511062697571942400655149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30014750263429256534206865 22511062697571942400655149)
        ·
          refine ⟨8441648511589478400245681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22511062697571942400655149 8441648511589478400245681)
          ·
            refine ⟨6331236383692108800184261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8441648511589478400245681 6331236383692108800184261)
            ·
              refine ⟨1187106821942270400034549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6331236383692108800184261 1187106821942270400034549)
              ·
                refine ⟨111291264557087850003239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1187106821942270400034549 111291264557087850003239)
                ·
                  rfl

theorem cell19_365747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_365747 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365747 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365747 prefixEnd_365747 := by exact prefixLift 365747
  have htrace : WordTrace (prefixWord ++ tailWord_365747) baseStart_365747 baseEnd_365747 := by
    simpa [prefixWord, tailWord_365747, baseEnd_365747] using wordTrace_append hprefix tailTrace_365747
  have hstable : (prefixWord ++ tailWord_365747).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365747).length < 2 ^ (prefixWord ++ tailWord_365747).sum := by decide
  have hdescent : baseEnd_365747 < baseStart_365747 := by decide
  rcases family_descends (prefixWord ++ tailWord_365747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365762 : List Nat := [3, 5, 1, 1, 9]
def baseStart_365762 : Nat := 118140960795 + 365762 * 2 ^ 59
def prefixEnd_365762 : Nat := 4983230072969 + 3 ^ 40 * 365762 * 2
def baseEnd_365762 : Nat := 4122067734428602209995

theorem tailTrace_365762 : CollatzResearch.WordTrace tailWord_365762 prefixEnd_365762 4122067734428602209995 := by
  unfold tailWord_365762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335109025228554005360885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8893624067276144014295693 3335109025228554005360885)
  ·
    refine ⟨312666471115176938002583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3335109025228554005360885 312666471115176938002583)
    ·
      refine ⟨468999706672765407003875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312666471115176938002583 468999706672765407003875)
      ·
        refine ⟨703499560009148110505813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468999706672765407003875 703499560009148110505813)
        ·
          refine ⟨4122067734428602209995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 703499560009148110505813 4122067734428602209995)
          ·
            rfl

theorem cell19_365762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 9].length) (baseStart_365762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365762 prefixEnd_365762 := by exact prefixLift 365762
  have htrace : WordTrace (prefixWord ++ tailWord_365762) baseStart_365762 baseEnd_365762 := by
    simpa [prefixWord, tailWord_365762, baseEnd_365762] using wordTrace_append hprefix tailTrace_365762
  have hstable : (prefixWord ++ tailWord_365762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365762).length < 2 ^ (prefixWord ++ tailWord_365762).sum := by decide
  have hdescent : baseEnd_365762 < baseStart_365762 := by decide
  rcases family_descends (prefixWord ++ tailWord_365762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365764 : List Nat := [2, 3, 3, 1, 3, 7]
def baseStart_365764 : Nat := 118140960795 + 365764 * 2 ^ 59
def prefixEnd_365764 : Nat := 4983230072969 + 3 ^ 40 * 365764 * 2
def baseEnd_365764 : Nat := 12366270822137427513935

theorem tailTrace_365764 : CollatzResearch.WordTrace tailWord_365764 prefixEnd_365764 12366270822137427513935 := by
  unfold tailWord_365764
  simp only [CollatzResearch.WordTrace]
  refine ⟨6670254523453485181508173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8893672697937980242010897 6670254523453485181508173)
  ·
    refine ⟨2501345446295056943065565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6670254523453485181508173 2501345446295056943065565)
    ·
      refine ⟨938004542360646353649587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2501345446295056943065565 938004542360646353649587)
      ·
        refine ⟨1407006813540969530474381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938004542360646353649587 1407006813540969530474381)
        ·
          refine ⟨527627555077863573927893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1407006813540969530474381 527627555077863573927893)
          ·
            refine ⟨12366270822137427513935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 527627555077863573927893 12366270822137427513935)
            ·
              rfl

theorem cell19_365764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 7].length) (baseStart_365764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365764 prefixEnd_365764 := by exact prefixLift 365764
  have htrace : WordTrace (prefixWord ++ tailWord_365764) baseStart_365764 baseEnd_365764 := by
    simpa [prefixWord, tailWord_365764, baseEnd_365764] using wordTrace_append hprefix tailTrace_365764
  have hstable : (prefixWord ++ tailWord_365764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365764).length < 2 ^ (prefixWord ++ tailWord_365764).sum := by decide
  have hdescent : baseEnd_365764 < baseStart_365764 := by decide
  rcases family_descends (prefixWord ++ tailWord_365764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365781 : List Nat := [1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_365781 : Nat := 118140960795 + 365781 * 2 ^ 59
def prefixEnd_365781 : Nat := 4983230072969 + 3 ^ 40 * 365781 * 2
def baseEnd_365781 : Nat := 111301610241385845247591

theorem tailTrace_365781 : CollatzResearch.WordTrace tailWord_365781 prefixEnd_365781 111301610241385845247591 := by
  unfold tailWord_365781
  simp only [CollatzResearch.WordTrace]
  refine ⟨13341129087845382266385197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8894086058563588177590131 13341129087845382266385197)
  ·
    refine ⟨5002923407942018349894449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13341129087845382266385197 5002923407942018349894449)
    ·
      refine ⟨3752192555956513762420837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5002923407942018349894449 3752192555956513762420837)
      ·
        refine ⟨703536104241846330453907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3752192555956513762420837 703536104241846330453907)
        ·
          refine ⟨1055304156362769495680861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703536104241846330453907 1055304156362769495680861)
          ·
            refine ⟨395739058636038560880323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1055304156362769495680861 395739058636038560880323)
            ·
              refine ⟨593608587954057841320485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395739058636038560880323 593608587954057841320485)
              ·
                refine ⟨111301610241385845247591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 593608587954057841320485 111301610241385845247591)
                ·
                  rfl

theorem cell19_365781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_365781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365781 prefixEnd_365781 := by exact prefixLift 365781
  have htrace : WordTrace (prefixWord ++ tailWord_365781) baseStart_365781 baseEnd_365781 := by
    simpa [prefixWord, tailWord_365781, baseEnd_365781] using wordTrace_append hprefix tailTrace_365781
  have hstable : (prefixWord ++ tailWord_365781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365781).length < 2 ^ (prefixWord ++ tailWord_365781).sum := by decide
  have hdescent : baseEnd_365781 < baseStart_365781 := by decide
  rcases family_descends (prefixWord ++ tailWord_365781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365823 : List Nat := [1, 1, 2, 2, 1, 6, 6]
def baseStart_365823 : Nat := 118140960795 + 365823 * 2 ^ 59
def prefixEnd_365823 : Nat := 4983230072969 + 3 ^ 40 * 365823 * 2
def baseEnd_365823 : Nat := 37104796734780730771381

theorem tailTrace_365823 : CollatzResearch.WordTrace tailWord_365823 prefixEnd_365823 37104796734780730771381 := by
  unfold tailWord_365823
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342660953693223439414123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8895107302462148959609415 13342660953693223439414123)
  ·
    refine ⟨20013991430539835159121185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13342660953693223439414123 20013991430539835159121185)
    ·
      refine ⟨15010493572904876369340889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20013991430539835159121185 15010493572904876369340889)
      ·
        refine ⟨11257870179678657277005667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15010493572904876369340889 11257870179678657277005667)
        ·
          refine ⟨16886805269517985915508501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11257870179678657277005667 16886805269517985915508501)
          ·
            refine ⟨791568997008655589789461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16886805269517985915508501 791568997008655589789461)
            ·
              refine ⟨37104796734780730771381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 791568997008655589789461 37104796734780730771381)
              ·
                rfl

theorem cell19_365823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_365823 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365823 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365823 prefixEnd_365823 := by exact prefixLift 365823
  have htrace : WordTrace (prefixWord ++ tailWord_365823) baseStart_365823 baseEnd_365823 := by
    simpa [prefixWord, tailWord_365823, baseEnd_365823] using wordTrace_append hprefix tailTrace_365823
  have hstable : (prefixWord ++ tailWord_365823).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365823).length < 2 ^ (prefixWord ++ tailWord_365823).sum := by decide
  have hdescent : baseEnd_365823 < baseStart_365823 := by decide
  rcases family_descends (prefixWord ++ tailWord_365823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365855 : List Nat := [1, 1, 2, 4, 5, 1, 2, 3]
def baseStart_365855 : Nat := 118140960795 + 365855 * 2 ^ 59
def prefixEnd_365855 : Nat := 4983230072969 + 3 ^ 40 * 365855 * 2
def baseEnd_365855 : Nat := 111324127318975599602945

theorem tailTrace_365855 : CollatzResearch.WordTrace tailWord_365855 prefixEnd_365855 111324127318975599602945 := by
  unfold tailWord_365855
  simp only [CollatzResearch.WordTrace]
  refine ⟨13343828089577292904579019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8895885393051528603052679 13343828089577292904579019)
  ·
    refine ⟨20015742134365939356868529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13343828089577292904579019 20015742134365939356868529)
    ·
      refine ⟨15011806600774454517651397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20015742134365939356868529 15011806600774454517651397)
      ·
        refine ⟨2814713737645210222059637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15011806600774454517651397 2814713737645210222059637)
        ·
          refine ⟨263879412904238458318091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2814713737645210222059637 263879412904238458318091)
          ·
            refine ⟨395819119356357687477137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263879412904238458318091 395819119356357687477137)
            ·
              refine ⟨296864339517268265607853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395819119356357687477137 296864339517268265607853)
              ·
                refine ⟨111324127318975599602945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296864339517268265607853 111324127318975599602945)
                ·
                  rfl

theorem cell19_365855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 3].length) (baseStart_365855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365855 prefixEnd_365855 := by exact prefixLift 365855
  have htrace : WordTrace (prefixWord ++ tailWord_365855) baseStart_365855 baseEnd_365855 := by
    simpa [prefixWord, tailWord_365855, baseEnd_365855] using wordTrace_append hprefix tailTrace_365855
  have hstable : (prefixWord ++ tailWord_365855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365855).length < 2 ^ (prefixWord ++ tailWord_365855).sum := by decide
  have hdescent : baseEnd_365855 < baseStart_365855 := by decide
  rcases family_descends (prefixWord ++ tailWord_365855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365859 : List Nat := [1, 1, 1, 4, 2, 3, 4, 3]
def baseStart_365859 : Nat := 118140960795 + 365859 * 2 ^ 59
def prefixEnd_365859 : Nat := 4983230072969 + 3 ^ 40 * 365859 * 2
def baseEnd_365859 : Nat := 111325344458304775514045

theorem tailTrace_365859 : CollatzResearch.WordTrace tailWord_365859 prefixEnd_365859 111325344458304775514045 := by
  unfold tailWord_365859
  simp only [CollatzResearch.WordTrace]
  refine ⟨13343973981562801587724631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8895982654375201058483087 13343973981562801587724631)
  ·
    refine ⟨20015960972344202381586947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13343973981562801587724631 20015960972344202381586947)
    ·
      refine ⟨30023941458516303572380421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20015960972344202381586947 30023941458516303572380421)
      ·
        refine ⟨5629489023471806919821329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30023941458516303572380421 5629489023471806919821329)
        ·
          refine ⟨4222116767603855189865997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5629489023471806919821329 4222116767603855189865997)
          ·
            refine ⟨1583293787851445696199749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4222116767603855189865997 1583293787851445696199749)
            ·
              refine ⟨296867585222146068037453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1583293787851445696199749 296867585222146068037453)
              ·
                refine ⟨111325344458304775514045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296867585222146068037453 111325344458304775514045)
                ·
                  rfl

theorem cell19_365859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_365859 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_365859 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_365859 prefixEnd_365859 := by exact prefixLift 365859
  have htrace : WordTrace (prefixWord ++ tailWord_365859) baseStart_365859 baseEnd_365859 := by
    simpa [prefixWord, tailWord_365859, baseEnd_365859] using wordTrace_append hprefix tailTrace_365859
  have hstable : (prefixWord ++ tailWord_365859).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365859).length < 2 ^ (prefixWord ++ tailWord_365859).sum := by decide
  have hdescent : baseEnd_365859 < baseStart_365859 := by decide
  rcases family_descends (prefixWord ++ tailWord_365859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366013 : List Nat := [1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_366013 : Nat := 118140960795 + 366013 * 2 ^ 59
def prefixEnd_366013 : Nat := 4983230072969 + 3 ^ 40 * 366013 * 2
def baseEnd_366013 : Nat := 111372204322478048091403

theorem tailTrace_366013 : CollatzResearch.WordTrace tailWord_366013 prefixEnd_366013 111372204322478048091403 := by
  unfold tailWord_366013
  simp only [CollatzResearch.WordTrace]
  refine ⟨13349590823004885888830693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8899727215336590592553795 13349590823004885888830693)
  ·
    refine ⟨2503048279313416104155755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13349590823004885888830693 2503048279313416104155755)
    ·
      refine ⟨3754572418970124156233633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2503048279313416104155755 3754572418970124156233633)
      ·
        refine ⟨2815929314227593117175225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3754572418970124156233633 2815929314227593117175225)
        ·
          refine ⟨2111946985670694837881419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2815929314227593117175225 2111946985670694837881419)
          ·
            refine ⟨3167920478506042256822129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111946985670694837881419 3167920478506042256822129)
            ·
              refine ⟨2375940358879531692616597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3167920478506042256822129 2375940358879531692616597)
              ·
                refine ⟨111372204322478048091403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2375940358879531692616597 111372204322478048091403)
                ·
                  rfl

theorem cell19_366013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_366013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366013 prefixEnd_366013 := by exact prefixLift 366013
  have htrace : WordTrace (prefixWord ++ tailWord_366013) baseStart_366013 baseEnd_366013 := by
    simpa [prefixWord, tailWord_366013, baseEnd_366013] using wordTrace_append hprefix tailTrace_366013
  have hstable : (prefixWord ++ tailWord_366013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366013).length < 2 ^ (prefixWord ++ tailWord_366013).sum := by decide
  have hdescent : baseEnd_366013 < baseStart_366013 := by decide
  rcases family_descends (prefixWord ++ tailWord_366013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366028 : List Nat := [2, 2, 1, 4, 2, 3, 2, 3]
def baseStart_366028 : Nat := 118140960795 + 366028 * 2 ^ 59
def prefixEnd_366028 : Nat := 4983230072969 + 3 ^ 40 * 366028 * 2
def baseEnd_366028 : Nat := 111376768594962457758029

theorem tailTrace_366028 : CollatzResearch.WordTrace tailWord_366028 prefixEnd_366028 111376768594962457758029 := by
  unfold tailWord_366028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6675068958975271725313369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8900091945300362300417825 6675068958975271725313369)
  ·
    refine ⟨5006301719231453793985027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6675068958975271725313369 5006301719231453793985027)
    ·
      refine ⟨7509452578847180690977541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5006301719231453793985027 7509452578847180690977541)
      ·
        refine ⟨1408022358533846379558289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7509452578847180690977541 1408022358533846379558289)
        ·
          refine ⟨1056016768900384784668717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408022358533846379558289 1056016768900384784668717)
          ·
            refine ⟨396006288337644294250769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1056016768900384784668717 396006288337644294250769)
            ·
              refine ⟨297004716253233220688077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396006288337644294250769 297004716253233220688077)
              ·
                refine ⟨111376768594962457758029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297004716253233220688077 111376768594962457758029)
                ·
                  rfl

theorem cell19_366028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_366028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366028 prefixEnd_366028 := by exact prefixLift 366028
  have htrace : WordTrace (prefixWord ++ tailWord_366028) baseStart_366028 baseEnd_366028 := by
    simpa [prefixWord, tailWord_366028, baseEnd_366028] using wordTrace_append hprefix tailTrace_366028
  have hstable : (prefixWord ++ tailWord_366028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366028).length < 2 ^ (prefixWord ++ tailWord_366028).sum := by decide
  have hdescent : baseEnd_366028 < baseStart_366028 := by decide
  rcases family_descends (prefixWord ++ tailWord_366028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366030 : List Nat := [4, 1, 1, 1, 2, 1, 6, 3]
def baseStart_366030 : Nat := 118140960795 + 366030 * 2 ^ 59
def prefixEnd_366030 : Nat := 4983230072969 + 3 ^ 40 * 366030 * 2
def baseEnd_366030 : Nat := 111377377164627045713579

theorem tailTrace_366030 : CollatzResearch.WordTrace tailWord_366030 prefixEnd_366030 111377377164627045713579 := by
  unfold tailWord_366030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668776357992912224024943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8900140575962198528133029 1668776357992912224024943)
  ·
    refine ⟨2503164536989368336037415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1668776357992912224024943 2503164536989368336037415)
    ·
      refine ⟨3754746805484052504056123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2503164536989368336037415 3754746805484052504056123)
      ·
        refine ⟨5632120208226078756084185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754746805484052504056123 5632120208226078756084185)
        ·
          refine ⟨4224090156169559067063139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5632120208226078756084185 4224090156169559067063139)
          ·
            refine ⟨6336135234254338600594709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224090156169559067063139 6336135234254338600594709)
            ·
              refine ⟨297006339105672121902877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6336135234254338600594709 297006339105672121902877)
              ·
                refine ⟨111377377164627045713579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297006339105672121902877 111377377164627045713579)
                ·
                  rfl

theorem cell19_366030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_366030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366030 prefixEnd_366030 := by exact prefixLift 366030
  have htrace : WordTrace (prefixWord ++ tailWord_366030) baseStart_366030 baseEnd_366030 := by
    simpa [prefixWord, tailWord_366030, baseEnd_366030] using wordTrace_append hprefix tailTrace_366030
  have hstable : (prefixWord ++ tailWord_366030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366030).length < 2 ^ (prefixWord ++ tailWord_366030).sum := by decide
  have hdescent : baseEnd_366030 < baseStart_366030 := by decide
  rcases family_descends (prefixWord ++ tailWord_366030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366051 : List Nat := [1, 1, 1, 6, 2, 1, 7]
def baseStart_366051 : Nat := 118140960795 + 366051 * 2 ^ 59
def prefixEnd_366051 : Nat := 4983230072969 + 3 ^ 40 * 366051 * 2
def baseEnd_366051 : Nat := 37127922382035073082285

theorem tailTrace_366051 : CollatzResearch.WordTrace tailWord_366051 prefixEnd_366051 37127922382035073082285 := by
  unfold tailWord_366051
  simp only [CollatzResearch.WordTrace]
  refine ⟨13350976796867218378714007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8900651197911478919142671 13350976796867218378714007)
  ·
    refine ⟨20026465195300827568071011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13350976796867218378714007 20026465195300827568071011)
    ·
      refine ⟨30039697792951241352106517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20026465195300827568071011 30039697792951241352106517)
      ·
        refine ⟨1408110834044589438379993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30039697792951241352106517 1408110834044589438379993)
        ·
          refine ⟨1056083125533442078784995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408110834044589438379993 1056083125533442078784995)
          ·
            refine ⟨1584124688300163118177493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056083125533442078784995 1584124688300163118177493)
            ·
              refine ⟨37127922382035073082285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1584124688300163118177493 37127922382035073082285)
              ·
                rfl

theorem cell19_366051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_366051 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366051 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366051 prefixEnd_366051 := by exact prefixLift 366051
  have htrace : WordTrace (prefixWord ++ tailWord_366051) baseStart_366051 baseEnd_366051 := by
    simpa [prefixWord, tailWord_366051, baseEnd_366051] using wordTrace_append hprefix tailTrace_366051
  have hstable : (prefixWord ++ tailWord_366051).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366051).length < 2 ^ (prefixWord ++ tailWord_366051).sum := by decide
  have hdescent : baseEnd_366051 < baseStart_366051 := by decide
  rcases family_descends (prefixWord ++ tailWord_366051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366222 : List Nat := [4, 1, 1, 3, 1, 2, 7]
def baseStart_366222 : Nat := 118140960795 + 366222 * 2 ^ 59
def prefixEnd_366222 : Nat := 4983230072969 + 3 ^ 40 * 366222 * 2
def baseEnd_366222 : Nat := 37145266617475829815463

theorem tailTrace_366222 : CollatzResearch.WordTrace tailWord_366222 prefixEnd_366222 37145266617475829815463 := by
  unfold tailWord_366222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669651709905964322898615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8904809119498476388792613 1669651709905964322898615)
  ·
    refine ⟨2504477564858946484347923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1669651709905964322898615 2504477564858946484347923)
    ·
      refine ⟨3756716347288419726521885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2504477564858946484347923 3756716347288419726521885)
      ·
        refine ⟨1408768630233157397445707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3756716347288419726521885 1408768630233157397445707)
        ·
          refine ⟨2113152945349736096168561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408768630233157397445707 2113152945349736096168561)
          ·
            refine ⟨1584864709012302072126421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113152945349736096168561 1584864709012302072126421)
            ·
              refine ⟨37145266617475829815463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1584864709012302072126421 37145266617475829815463)
              ·
                rfl

theorem cell19_366222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_366222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366222 prefixEnd_366222 := by exact prefixLift 366222
  have htrace : WordTrace (prefixWord ++ tailWord_366222) baseStart_366222 baseEnd_366222 := by
    simpa [prefixWord, tailWord_366222, baseEnd_366222] using wordTrace_append hprefix tailTrace_366222
  have hstable : (prefixWord ++ tailWord_366222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366222).length < 2 ^ (prefixWord ++ tailWord_366222).sum := by decide
  have hdescent : baseEnd_366222 < baseStart_366222 := by decide
  rcases family_descends (prefixWord ++ tailWord_366222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366241 : List Nat := [1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_366241 : Nat := 118140960795 + 366241 * 2 ^ 59
def prefixEnd_366241 : Nat := 4983230072969 + 3 ^ 40 * 366241 * 2
def baseEnd_366241 : Nat := 111441581264241075024115

theorem tailTrace_366241 : CollatzResearch.WordTrace tailWord_366241 prefixEnd_366241 111441581264241075024115 := by
  unfold tailWord_366241
  simp only [CollatzResearch.WordTrace]
  refine ⟨13357906666178880828130577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8905271110785920552087051 13357906666178880828130577)
  ·
    refine ⟨10018429999634160621097933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13357906666178880828130577 10018429999634160621097933)
    ·
      refine ⟨3756911249862810232911725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10018429999634160621097933 3756911249862810232911725)
      ·
        refine ⟨1408841718698553837341897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3756911249862810232911725 1408841718698553837341897)
        ·
          refine ⟨1056631289023915378006423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408841718698553837341897 1056631289023915378006423)
          ·
            refine ⟨1584946933535873067009635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056631289023915378006423 1584946933535873067009635)
            ·
              refine ⟨2377420400303809600514453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584946933535873067009635 2377420400303809600514453)
              ·
                refine ⟨111441581264241075024115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2377420400303809600514453 111441581264241075024115)
                ·
                  rfl

theorem cell19_366241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_366241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366241 prefixEnd_366241 := by exact prefixLift 366241
  have htrace : WordTrace (prefixWord ++ tailWord_366241) baseStart_366241 baseEnd_366241 := by
    simpa [prefixWord, tailWord_366241, baseEnd_366241] using wordTrace_append hprefix tailTrace_366241
  have hstable : (prefixWord ++ tailWord_366241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366241).length < 2 ^ (prefixWord ++ tailWord_366241).sum := by decide
  have hdescent : baseEnd_366241 < baseStart_366241 := by decide
  rcases family_descends (prefixWord ++ tailWord_366241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366298 : List Nat := [3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_366298 : Nat := 118140960795 + 366298 * 2 ^ 59
def prefixEnd_366298 : Nat := 4983230072969 + 3 ^ 40 * 366298 * 2
def baseEnd_366298 : Nat := 111458925499681831757293

theorem tailTrace_366298 : CollatzResearch.WordTrace tailWord_366298 prefixEnd_366298 111458925499681831757293 := by
  unfold tailWord_366298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339996406743094890738887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8906657084648253041970365 3339996406743094890738887)
  ·
    refine ⟨5009994610114642336108331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3339996406743094890738887 5009994610114642336108331)
    ·
      refine ⟨7514991915171963504162497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5009994610114642336108331 7514991915171963504162497)
      ·
        refine ⟨5636243936378972628121873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7514991915171963504162497 5636243936378972628121873)
        ·
          refine ⟨4227182952284229471091405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5636243936378972628121873 4227182952284229471091405)
          ·
            refine ⟨1585193607106586051659277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4227182952284229471091405 1585193607106586051659277)
            ·
              refine ⟨594447602664969769372229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1585193607106586051659277 594447602664969769372229)
              ·
                refine ⟨111458925499681831757293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 594447602664969769372229 111458925499681831757293)
                ·
                  rfl

theorem cell19_366298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_366298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366298 prefixEnd_366298 := by exact prefixLift 366298
  have htrace : WordTrace (prefixWord ++ tailWord_366298) baseStart_366298 baseEnd_366298 := by
    simpa [prefixWord, tailWord_366298, baseEnd_366298] using wordTrace_append hprefix tailTrace_366298
  have hstable : (prefixWord ++ tailWord_366298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366298).length < 2 ^ (prefixWord ++ tailWord_366298).sum := by decide
  have hdescent : baseEnd_366298 < baseStart_366298 := by decide
  rcases family_descends (prefixWord ++ tailWord_366298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366334 : List Nat := [4, 2, 2, 1, 3, 1, 6]
def baseStart_366334 : Nat := 118140960795 + 366334 * 2 ^ 59
def prefixEnd_366334 : Nat := 4983230072969 + 3 ^ 40 * 366334 * 2
def baseEnd_366334 : Nat := 37156626584548138319065

theorem tailTrace_366334 : CollatzResearch.WordTrace tailWord_366334 prefixEnd_366334 37156626584548138319065 := by
  unfold tailWord_366334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670162331855244713908257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8907532436561305140844037 1670162331855244713908257)
  ·
    refine ⟨1252621748891433535431193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1670162331855244713908257 1252621748891433535431193)
    ·
      refine ⟨939466311668575151573395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1252621748891433535431193 939466311668575151573395)
      ·
        refine ⟨1409199467502862727360093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939466311668575151573395 1409199467502862727360093)
        ·
          refine ⟨528449800313573522760035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1409199467502862727360093 528449800313573522760035)
          ·
            refine ⟨792674700470360284140053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528449800313573522760035 792674700470360284140053)
            ·
              refine ⟨37156626584548138319065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 792674700470360284140053 37156626584548138319065)
              ·
                rfl

theorem cell19_366334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_366334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366334 prefixEnd_366334 := by exact prefixLift 366334
  have htrace : WordTrace (prefixWord ++ tailWord_366334) baseStart_366334 baseEnd_366334 := by
    simpa [prefixWord, tailWord_366334, baseEnd_366334] using wordTrace_append hprefix tailTrace_366334
  have hstable : (prefixWord ++ tailWord_366334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366334).length < 2 ^ (prefixWord ++ tailWord_366334).sum := by decide
  have hdescent : baseEnd_366334 < baseStart_366334 := by decide
  rcases family_descends (prefixWord ++ tailWord_366334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366366 : List Nat := [4, 3, 2, 2, 1, 2, 2, 3]
def baseStart_366366 : Nat := 118140960795 + 366366 * 2 ^ 59
def prefixEnd_366366 : Nat := 4983230072969 + 3 ^ 40 * 366366 * 2
def baseEnd_366366 : Nat := 111479616868277822245997

theorem tailTrace_366366 : CollatzResearch.WordTrace tailWord_366366 prefixEnd_366366 111479616868277822245997 := by
  unfold tailWord_366366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670308223840753397053869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8908310527150684784287301 1670308223840753397053869)
  ·
    refine ⟨626365583940282523895201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1670308223840753397053869 626365583940282523895201)
    ·
      refine ⟨469774187955211892921401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 626365583940282523895201 469774187955211892921401)
      ·
        refine ⟨352330640966408919691051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469774187955211892921401 352330640966408919691051)
        ·
          refine ⟨528495961449613379536577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352330640966408919691051 528495961449613379536577)
          ·
            refine ⟨396371971087210034652433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528495961449613379536577 396371971087210034652433)
            ·
              refine ⟨297278978315407525989325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396371971087210034652433 297278978315407525989325)
              ·
                refine ⟨111479616868277822245997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297278978315407525989325 111479616868277822245997)
                ·
                  rfl

theorem cell19_366366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_366366 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366366 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366366 prefixEnd_366366 := by exact prefixLift 366366
  have htrace : WordTrace (prefixWord ++ tailWord_366366) baseStart_366366 baseEnd_366366 := by
    simpa [prefixWord, tailWord_366366, baseEnd_366366] using wordTrace_append hprefix tailTrace_366366
  have hstable : (prefixWord ++ tailWord_366366).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366366).length < 2 ^ (prefixWord ++ tailWord_366366).sum := by decide
  have hdescent : baseEnd_366366 < baseStart_366366 := by decide
  rcases family_descends (prefixWord ++ tailWord_366366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366372 : List Nat := [2, 3, 1, 3, 2, 1, 4, 3]
def baseStart_366372 : Nat := 118140960795 + 366372 * 2 ^ 59
def prefixEnd_366372 : Nat := 4983230072969 + 3 ^ 40 * 366372 * 2
def baseEnd_366372 : Nat := 111481442577271586112647

theorem tailTrace_366372 : CollatzResearch.WordTrace tailWord_366372 prefixEnd_366372 111481442577271586112647 := by
  unfold tailWord_366372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6681342314352145100574685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8908456419136193467432913 6681342314352145100574685)
  ·
    refine ⟨2505503367882054412715507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6681342314352145100574685 2505503367882054412715507)
    ·
      refine ⟨3758255051823081619073261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2505503367882054412715507 3758255051823081619073261)
      ·
        refine ⟨1409345644433655607152473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3758255051823081619073261 1409345644433655607152473)
        ·
          refine ⟨1057009233325241705364355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1409345644433655607152473 1057009233325241705364355)
          ·
            refine ⟨1585513849987862558046533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057009233325241705364355 1585513849987862558046533)
            ·
              refine ⟨297283846872724229633725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1585513849987862558046533 297283846872724229633725)
              ·
                refine ⟨111481442577271586112647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297283846872724229633725 111481442577271586112647)
                ·
                  rfl

theorem cell19_366372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_366372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366372 prefixEnd_366372 := by exact prefixLift 366372
  have htrace : WordTrace (prefixWord ++ tailWord_366372) baseStart_366372 baseEnd_366372 := by
    simpa [prefixWord, tailWord_366372, baseEnd_366372] using wordTrace_append hprefix tailTrace_366372
  have hstable : (prefixWord ++ tailWord_366372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366372).length < 2 ^ (prefixWord ++ tailWord_366372).sum := by decide
  have hdescent : baseEnd_366372 < baseStart_366372 := by decide
  rcases family_descends (prefixWord ++ tailWord_366372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366433 : List Nat := [1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_366433 : Nat := 118140960795 + 366433 * 2 ^ 59
def prefixEnd_366433 : Nat := 4983230072969 + 3 ^ 40 * 366433 * 2
def baseEnd_366433 : Nat := 111500003952041518756925

theorem tailTrace_366433 : CollatzResearch.WordTrace tailWord_366433 prefixEnd_366433 111500003952041518756925 := by
  unfold tailWord_366433
  simp only [CollatzResearch.WordTrace]
  refine ⟨13364909481483297619119953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8909939654322198412746635 13364909481483297619119953)
  ·
    refine ⟨10023682111112473214339965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13364909481483297619119953 10023682111112473214339965)
    ·
      refine ⟨3758880791667177455377487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10023682111112473214339965 3758880791667177455377487)
      ·
        refine ⟨5638321187500766183066231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3758880791667177455377487 5638321187500766183066231)
        ·
          refine ⟨8457481781251149274599347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5638321187500766183066231 8457481781251149274599347)
          ·
            refine ⟨12686222671876723911899021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8457481781251149274599347 12686222671876723911899021)
            ·
              refine ⟨4757333501953771466962133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12686222671876723911899021 4757333501953771466962133)
              ·
                refine ⟨111500003952041518756925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4757333501953771466962133 111500003952041518756925)
                ·
                  rfl

theorem cell19_366433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_366433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366433 prefixEnd_366433 := by exact prefixLift 366433
  have htrace : WordTrace (prefixWord ++ tailWord_366433) baseStart_366433 baseEnd_366433 := by
    simpa [prefixWord, tailWord_366433, baseEnd_366433] using wordTrace_append hprefix tailTrace_366433
  have hstable : (prefixWord ++ tailWord_366433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366433).length < 2 ^ (prefixWord ++ tailWord_366433).sum := by decide
  have hdescent : baseEnd_366433 < baseStart_366433 := by decide
  rcases family_descends (prefixWord ++ tailWord_366433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366465 : List Nat := [1, 2, 4, 4, 1, 2, 1, 4]
def baseStart_366465 : Nat := 118140960795 + 366465 * 2 ^ 59
def prefixEnd_366465 : Nat := 4983230072969 + 3 ^ 40 * 366465 * 2
def baseEnd_366465 : Nat := 111509741066674926045727

theorem tailTrace_366465 : CollatzResearch.WordTrace tailWord_366465 prefixEnd_366465 111509741066674926045727 := by
  unfold tailWord_366465
  simp only [CollatzResearch.WordTrace]
  refine ⟨13366076617367367084284849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8910717744911578056189899 13366076617367367084284849)
  ·
    refine ⟨10024557463025525313213637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13366076617367367084284849 10024557463025525313213637)
    ·
      refine ⟨1879604524317285996227557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10024557463025525313213637 1879604524317285996227557)
      ·
        refine ⟨352425848309491124292667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1879604524317285996227557 352425848309491124292667)
        ·
          refine ⟨528638772464236686439001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352425848309491124292667 528638772464236686439001)
          ·
            refine ⟨396479079348177514829251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528638772464236686439001 396479079348177514829251)
            ·
              refine ⟨594718619022266272243877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396479079348177514829251 594718619022266272243877)
              ·
                refine ⟨111509741066674926045727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 594718619022266272243877 111509741066674926045727)
                ·
                  rfl

theorem cell19_366465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_366465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366465 prefixEnd_366465 := by exact prefixLift 366465
  have htrace : WordTrace (prefixWord ++ tailWord_366465) baseStart_366465 baseEnd_366465 := by
    simpa [prefixWord, tailWord_366465, baseEnd_366465] using wordTrace_append hprefix tailTrace_366465
  have hstable : (prefixWord ++ tailWord_366465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366465).length < 2 ^ (prefixWord ++ tailWord_366465).sum := by decide
  have hdescent : baseEnd_366465 < baseStart_366465 := by decide
  rcases family_descends (prefixWord ++ tailWord_366465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366528 : List Nat := [2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_366528 : Nat := 118140960795 + 366528 * 2 ^ 59
def prefixEnd_366528 : Nat := 4983230072969 + 3 ^ 40 * 366528 * 2
def baseEnd_366528 : Nat := 111528911011109446645555

theorem tailTrace_366528 : CollatzResearch.WordTrace tailWord_366528 prefixEnd_366528 111528911011109446645555 := by
  unfold tailWord_366528
  simp only [CollatzResearch.WordTrace]
  refine ⟨6684187208069564421914119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8912249610759419229218825 6684187208069564421914119)
  ·
    refine ⟨10026280812104346632871179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6684187208069564421914119 10026280812104346632871179)
    ·
      refine ⟨15039421218156519949306769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10026280812104346632871179 15039421218156519949306769)
      ·
        refine ⟨11279565913617389961980077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15039421218156519949306769 11279565913617389961980077)
        ·
          refine ⟨4229837217606521235742529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11279565913617389961980077 4229837217606521235742529)
          ·
            refine ⟨3172377913204890926806897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4229837217606521235742529 3172377913204890926806897)
            ·
              refine ⟨2379283434903668195105173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3172377913204890926806897 2379283434903668195105173)
              ·
                refine ⟨111528911011109446645555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2379283434903668195105173 111528911011109446645555)
                ·
                  rfl

theorem cell19_366528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_366528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366528 prefixEnd_366528 := by exact prefixLift 366528
  have htrace : WordTrace (prefixWord ++ tailWord_366528) baseStart_366528 baseEnd_366528 := by
    simpa [prefixWord, tailWord_366528, baseEnd_366528] using wordTrace_append hprefix tailTrace_366528
  have hstable : (prefixWord ++ tailWord_366528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366528).length < 2 ^ (prefixWord ++ tailWord_366528).sum := by decide
  have hdescent : baseEnd_366528 < baseStart_366528 := by decide
  rcases family_descends (prefixWord ++ tailWord_366528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366585 : List Nat := [1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_366585 : Nat := 118140960795 + 366585 * 2 ^ 59
def prefixEnd_366585 : Nat := 4983230072969 + 3 ^ 40 * 366585 * 2
def baseEnd_366585 : Nat := 111546255246550203378733

theorem tailTrace_366585 : CollatzResearch.WordTrace tailWord_366585 prefixEnd_366585 111546255246550203378733 := by
  unfold tailWord_366585
  simp only [CollatzResearch.WordTrace]
  refine ⟨13370453376932627578653209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8913635584621751719102139 13370453376932627578653209)
  ·
    refine ⟨10027840032699470683989907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13370453376932627578653209 10027840032699470683989907)
    ·
      refine ⟨15041760049049206025984861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10027840032699470683989907 15041760049049206025984861)
      ·
        refine ⟨5640660018393452259744323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15041760049049206025984861 5640660018393452259744323)
        ·
          refine ⟨8460990027590178389616485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640660018393452259744323 8460990027590178389616485)
          ·
            refine ⟨1586435630173158448053091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8460990027590178389616485 1586435630173158448053091)
            ·
              refine ⟨2379653445259737672079637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586435630173158448053091 2379653445259737672079637)
              ·
                refine ⟨111546255246550203378733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2379653445259737672079637 111546255246550203378733)
                ·
                  rfl

theorem cell19_366585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_366585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366585 prefixEnd_366585 := by exact prefixLift 366585
  have htrace : WordTrace (prefixWord ++ tailWord_366585) baseStart_366585 baseEnd_366585 := by
    simpa [prefixWord, tailWord_366585, baseEnd_366585] using wordTrace_append hprefix tailTrace_366585
  have hstable : (prefixWord ++ tailWord_366585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366585).length < 2 ^ (prefixWord ++ tailWord_366585).sum := by decide
  have hdescent : baseEnd_366585 < baseStart_366585 := by decide
  rcases family_descends (prefixWord ++ tailWord_366585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366604 : List Nat := [2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_366604 : Nat := 118140960795 + 366604 * 2 ^ 59
def prefixEnd_366604 : Nat := 4983230072969 + 3 ^ 40 * 366604 * 2
def baseEnd_366604 : Nat := 111552036658363788956459

theorem tailTrace_366604 : CollatzResearch.WordTrace tailWord_366604 prefixEnd_366604 111552036658363788956459 := by
  unfold tailWord_366604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6685573181931896911797433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8914097575909195882396577 6685573181931896911797433)
  ·
    refine ⟨5014179886448922683848075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6685573181931896911797433 5014179886448922683848075)
    ·
      refine ⟨7521269829673384025772113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5014179886448922683848075 7521269829673384025772113)
      ·
        refine ⟨5640952372255038019329085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7521269829673384025772113 5640952372255038019329085)
        ·
          refine ⟨2115357139595639257248407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5640952372255038019329085 2115357139595639257248407)
          ·
            refine ⟨3173035709393458885872611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115357139595639257248407 3173035709393458885872611)
            ·
              refine ⟨4759553564090188328808917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173035709393458885872611 4759553564090188328808917)
              ·
                refine ⟨111552036658363788956459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4759553564090188328808917 111552036658363788956459)
                ·
                  rfl

theorem cell19_366604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_366604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366604 prefixEnd_366604 := by exact prefixLift 366604
  have htrace : WordTrace (prefixWord ++ tailWord_366604) baseStart_366604 baseEnd_366604 := by
    simpa [prefixWord, tailWord_366604, baseEnd_366604] using wordTrace_append hprefix tailTrace_366604
  have hstable : (prefixWord ++ tailWord_366604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366604).length < 2 ^ (prefixWord ++ tailWord_366604).sum := by decide
  have hdescent : baseEnd_366604 < baseStart_366604 := by decide
  rcases family_descends (prefixWord ++ tailWord_366604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366638 : List Nat := [4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_366638 : Nat := 118140960795 + 366638 * 2 ^ 59
def prefixEnd_366638 : Nat := 4983230072969 + 3 ^ 40 * 366638 * 2
def baseEnd_366638 : Nat := 111562382342661784200811

theorem tailTrace_366638 : CollatzResearch.WordTrace tailWord_366638 prefixEnd_366638 111562382342661784200811 := by
  unfold tailWord_366638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671548305717577203791571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8914924297160411753555045 1671548305717577203791571)
  ·
    refine ⟨2507322458576365805687357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1671548305717577203791571 2507322458576365805687357)
    ·
      refine ⟨940245921966137177132759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2507322458576365805687357 940245921966137177132759)
      ·
        refine ⟨1410368882949205765699139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940245921966137177132759 1410368882949205765699139)
        ·
          refine ⟨2115553324423808648548709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410368882949205765699139 2115553324423808648548709)
          ·
            refine ⟨396666248329464121602883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2115553324423808648548709 396666248329464121602883)
            ·
              refine ⟨594999372494196182404325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396666248329464121602883 594999372494196182404325)
              ·
                refine ⟨111562382342661784200811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 594999372494196182404325 111562382342661784200811)
                ·
                  rfl

theorem cell19_366638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_366638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366638 prefixEnd_366638 := by exact prefixLift 366638
  have htrace : WordTrace (prefixWord ++ tailWord_366638) baseStart_366638 baseEnd_366638 := by
    simpa [prefixWord, tailWord_366638, baseEnd_366638] using wordTrace_append hprefix tailTrace_366638
  have hstable : (prefixWord ++ tailWord_366638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366638).length < 2 ^ (prefixWord ++ tailWord_366638).sum := by decide
  have hdescent : baseEnd_366638 < baseStart_366638 := by decide
  rcases family_descends (prefixWord ++ tailWord_366638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366640 : List Nat := [2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_366640 : Nat := 118140960795 + 366640 * 2 ^ 59
def prefixEnd_366640 : Nat := 4983230072969 + 3 ^ 40 * 366640 * 2
def baseEnd_366640 : Nat := 111562990912326372156361

theorem tailTrace_366640 : CollatzResearch.WordTrace tailWord_366640 prefixEnd_366640 111562990912326372156361 := by
  unfold tailWord_366640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6686229695866685985952687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8914972927822247981270249 6686229695866685985952687)
  ·
    refine ⟨10029344543800028978929031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6686229695866685985952687 10029344543800028978929031)
    ·
      refine ⟨15044016815700043468393547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10029344543800028978929031 15044016815700043468393547)
      ·
        refine ⟨22566025223550065202590321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15044016815700043468393547 22566025223550065202590321)
        ·
          refine ⟨16924518917662548901942741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22566025223550065202590321 16924518917662548901942741)
          ·
            refine ⟨396668412132715989889283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16924518917662548901942741 396668412132715989889283)
            ·
              refine ⟨595002618199073984833925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396668412132715989889283 595002618199073984833925)
              ·
                refine ⟨111562990912326372156361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595002618199073984833925 111562990912326372156361)
                ·
                  rfl

theorem cell19_366640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_366640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366640 prefixEnd_366640 := by exact prefixLift 366640
  have htrace : WordTrace (prefixWord ++ tailWord_366640) baseStart_366640 baseEnd_366640 := by
    simpa [prefixWord, tailWord_366640, baseEnd_366640] using wordTrace_append hprefix tailTrace_366640
  have hstable : (prefixWord ++ tailWord_366640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366640).length < 2 ^ (prefixWord ++ tailWord_366640).sum := by decide
  have hdescent : baseEnd_366640 < baseStart_366640 := by decide
  rcases family_descends (prefixWord ++ tailWord_366640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366657 : List Nat := [1, 2, 5, 1, 2, 2, 3, 3]
def baseStart_366657 : Nat := 118140960795 + 366657 * 2 ^ 59
def prefixEnd_366657 : Nat := 4983230072969 + 3 ^ 40 * 366657 * 2
def baseEnd_366657 : Nat := 111568163754475369778537

theorem tailTrace_366657 : CollatzResearch.WordTrace tailWord_366657 prefixEnd_366657 111568163754475369778537 := by
  unfold tailWord_366657
  simp only [CollatzResearch.WordTrace]
  refine ⟨13373079432671783875274225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8915386288447855916849483 13373079432671783875274225)
  ·
    refine ⟨10029809574503837906455669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13373079432671783875274225 10029809574503837906455669)
    ·
      refine ⟨940294647609734803730219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10029809574503837906455669 940294647609734803730219)
      ·
        refine ⟨1410441971414602205595329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940294647609734803730219 1410441971414602205595329)
        ·
          refine ⟨1057831478560951654196497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410441971414602205595329 1057831478560951654196497)
          ·
            refine ⟨793373608920713740647373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057831478560951654196497 793373608920713740647373)
            ·
              refine ⟨297515103345267652742765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 793373608920713740647373 297515103345267652742765)
              ·
                refine ⟨111568163754475369778537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297515103345267652742765 111568163754475369778537)
                ·
                  rfl

theorem cell19_366657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_366657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366657 prefixEnd_366657 := by exact prefixLift 366657
  have htrace : WordTrace (prefixWord ++ tailWord_366657) baseStart_366657 baseEnd_366657 := by
    simpa [prefixWord, tailWord_366657, baseEnd_366657] using wordTrace_append hprefix tailTrace_366657
  have hstable : (prefixWord ++ tailWord_366657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366657).length < 2 ^ (prefixWord ++ tailWord_366657).sum := by decide
  have hdescent : baseEnd_366657 < baseStart_366657 := by decide
  rcases family_descends (prefixWord ++ tailWord_366657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366680 : List Nat := [2, 1, 2, 2, 1, 5, 6]
def baseStart_366680 : Nat := 118140960795 + 366680 * 2 ^ 59
def prefixEnd_366680 : Nat := 4983230072969 + 3 ^ 40 * 366680 * 2
def baseEnd_366680 : Nat := 37191720768539377089121

theorem tailTrace_366680 : CollatzResearch.WordTrace tailWord_366680 prefixEnd_366680 37191720768539377089121 := by
  unfold tailWord_366680
  simp only [CollatzResearch.WordTrace]
  refine ⟨6686959155794229401680747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8915945541058972535574329 6686959155794229401680747)
  ·
    refine ⟨10030438733691344102521121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6686959155794229401680747 10030438733691344102521121)
    ·
      refine ⟨7522829050268508076890841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10030438733691344102521121 7522829050268508076890841)
      ·
        refine ⟨5642121787701381057668131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7522829050268508076890841 5642121787701381057668131)
        ·
          refine ⟨8463182681552071586502197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642121787701381057668131 8463182681552071586502197)
          ·
            refine ⟨793423376395506711234581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8463182681552071586502197 793423376395506711234581)
            ·
              refine ⟨37191720768539377089121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 793423376395506711234581 37191720768539377089121)
              ·
                rfl

theorem cell19_366680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_366680 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366680 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366680 prefixEnd_366680 := by exact prefixLift 366680
  have htrace : WordTrace (prefixWord ++ tailWord_366680) baseStart_366680 baseEnd_366680 := by
    simpa [prefixWord, tailWord_366680, baseEnd_366680] using wordTrace_append hprefix tailTrace_366680
  have hstable : (prefixWord ++ tailWord_366680).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366680).length < 2 ^ (prefixWord ++ tailWord_366680).sum := by decide
  have hdescent : baseEnd_366680 < baseStart_366680 := by decide
  rcases family_descends (prefixWord ++ tailWord_366680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366716 : List Nat := [2, 2, 2, 1, 1, 4, 4, 3]
def baseStart_366716 : Nat := 118140960795 + 366716 * 2 ^ 59
def prefixEnd_366716 : Nat := 4983230072969 + 3 ^ 40 * 366716 * 2
def baseEnd_366716 : Nat := 111586116559580714467265

theorem tailTrace_366716 : CollatzResearch.WordTrace tailWord_366716 prefixEnd_366716 111586116559580714467265 := by
  unfold tailWord_366716
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687615669729018475836001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8916820892972024634448001 6687615669729018475836001)
  ·
    refine ⟨5015711752296763856877001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6687615669729018475836001 5015711752296763856877001)
    ·
      refine ⟨3761783814222572892657751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5015711752296763856877001 3761783814222572892657751)
      ·
        refine ⟨5642675721333859338986627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761783814222572892657751 5642675721333859338986627)
        ·
          refine ⟨8464013582000789008479941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642675721333859338986627 8464013582000789008479941)
          ·
            refine ⟨1587002546625147939089989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8464013582000789008479941 1587002546625147939089989)
            ·
              refine ⟨297562977492215238579373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1587002546625147939089989 297562977492215238579373)
              ·
                refine ⟨111586116559580714467265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297562977492215238579373 111586116559580714467265)
                ·
                  rfl

theorem cell19_366716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_366716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366716 prefixEnd_366716 := by exact prefixLift 366716
  have htrace : WordTrace (prefixWord ++ tailWord_366716) baseStart_366716 baseEnd_366716 := by
    simpa [prefixWord, tailWord_366716, baseEnd_366716] using wordTrace_append hprefix tailTrace_366716
  have hstable : (prefixWord ++ tailWord_366716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366716).length < 2 ^ (prefixWord ++ tailWord_366716).sum := by decide
  have hdescent : baseEnd_366716 < baseStart_366716 := by decide
  rcases family_descends (prefixWord ++ tailWord_366716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366754 : List Nat := [3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_366754 : Nat := 118140960795 + 366754 * 2 ^ 59
def prefixEnd_366754 : Nat := 4983230072969 + 3 ^ 40 * 366754 * 2
def baseEnd_366754 : Nat := 111597679383207885622717

theorem tailTrace_366754 : CollatzResearch.WordTrace tailWord_366754 prefixEnd_366754 111597679383207885622717 := by
  unfold tailWord_366754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344154328330092360388829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8917744875546912961036877 3344154328330092360388829)
  ·
    refine ⟨1254057873123784635145811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3344154328330092360388829 1254057873123784635145811)
    ·
      refine ⟨1881086809685676952718717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1254057873123784635145811 1881086809685676952718717)
      ·
        refine ⟨705407553632128857269519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1881086809685676952718717 705407553632128857269519)
        ·
          refine ⟨1058111330448193285904279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705407553632128857269519 1058111330448193285904279)
          ·
            refine ⟨1587166995672289928856419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058111330448193285904279 1587166995672289928856419)
            ·
              refine ⟨2380750493508434893284629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587166995672289928856419 2380750493508434893284629)
              ·
                refine ⟨111597679383207885622717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2380750493508434893284629 111597679383207885622717)
                ·
                  rfl

theorem cell19_366754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_366754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366754 prefixEnd_366754 := by exact prefixLift 366754
  have htrace : WordTrace (prefixWord ++ tailWord_366754) baseStart_366754 baseEnd_366754 := by
    simpa [prefixWord, tailWord_366754, baseEnd_366754] using wordTrace_append hprefix tailTrace_366754
  have hstable : (prefixWord ++ tailWord_366754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366754).length < 2 ^ (prefixWord ++ tailWord_366754).sum := by decide
  have hdescent : baseEnd_366754 < baseStart_366754 := by decide
  rcases family_descends (prefixWord ++ tailWord_366754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366775 : List Nat := [1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_366775 : Nat := 118140960795 + 366775 * 2 ^ 59
def prefixEnd_366775 : Nat := 4983230072969 + 3 ^ 40 * 366775 * 2
def baseEnd_366775 : Nat := 111604069364686059155993

theorem tailTrace_366775 : CollatzResearch.WordTrace tailWord_366775 prefixEnd_366775 111604069364686059155993 := by
  unfold tailWord_366775
  simp only [CollatzResearch.WordTrace]
  refine ⟨13377383246244290028069779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8918255497496193352046519 13377383246244290028069779)
  ·
    refine ⟨20066074869366435042104669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13377383246244290028069779 20066074869366435042104669)
    ·
      refine ⟨7524778076012413140789251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20066074869366435042104669 7524778076012413140789251)
      ·
        refine ⟨11287167114018619711183877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7524778076012413140789251 11287167114018619711183877)
        ·
          refine ⟨2116343833878491195846977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11287167114018619711183877 2116343833878491195846977)
          ·
            refine ⟨1587257875408868396885233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2116343833878491195846977 1587257875408868396885233)
            ·
              refine ⟨1190443406556651297663925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587257875408868396885233 1190443406556651297663925)
              ·
                refine ⟨111604069364686059155993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1190443406556651297663925 111604069364686059155993)
                ·
                  rfl

theorem cell19_366775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_366775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366775 prefixEnd_366775 := by exact prefixLift 366775
  have htrace : WordTrace (prefixWord ++ tailWord_366775) baseStart_366775 baseEnd_366775 := by
    simpa [prefixWord, tailWord_366775, baseEnd_366775] using wordTrace_append hprefix tailTrace_366775
  have hstable : (prefixWord ++ tailWord_366775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366775).length < 2 ^ (prefixWord ++ tailWord_366775).sum := by decide
  have hdescent : baseEnd_366775 < baseStart_366775 := by decide
  rcases family_descends (prefixWord ++ tailWord_366775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366885 : List Nat := [1, 3, 1, 2, 5, 2, 2, 3]
def baseStart_366885 : Nat := 118140960795 + 366885 * 2 ^ 59
def prefixEnd_366885 : Nat := 4983230072969 + 3 ^ 40 * 366885 * 2
def baseEnd_366885 : Nat := 111637540696238396711249

theorem tailTrace_366885 : CollatzResearch.WordTrace tailWord_366885 prefixEnd_366885 111637540696238396711249 := by
  unfold tailWord_366885
  simp only [CollatzResearch.WordTrace]
  refine ⟨13381395275845778814574109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8920930183897185876382739 13381395275845778814574109)
  ·
    refine ⟨5018023228442167055465291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13381395275845778814574109 5018023228442167055465291)
    ·
      refine ⟨7527034842663250583197937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5018023228442167055465291 7527034842663250583197937)
      ·
        refine ⟨5645276131997437937398453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7527034842663250583197937 5645276131997437937398453)
        ·
          refine ⟨529244637374759806631105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5645276131997437937398453 529244637374759806631105)
          ·
            refine ⟨396933478031069854973329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529244637374759806631105 396933478031069854973329)
            ·
              refine ⟨297700108523302391229997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396933478031069854973329 297700108523302391229997)
              ·
                refine ⟨111637540696238396711249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297700108523302391229997 111637540696238396711249)
                ·
                  rfl

theorem cell19_366885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_366885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366885 prefixEnd_366885 := by exact prefixLift 366885
  have htrace : WordTrace (prefixWord ++ tailWord_366885) baseStart_366885 baseEnd_366885 := by
    simpa [prefixWord, tailWord_366885, baseEnd_366885] using wordTrace_append hprefix tailTrace_366885
  have hstable : (prefixWord ++ tailWord_366885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366885).length < 2 ^ (prefixWord ++ tailWord_366885).sum := by decide
  have hdescent : baseEnd_366885 < baseStart_366885 := by decide
  rcases family_descends (prefixWord ++ tailWord_366885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366965 : List Nat := [1, 3, 4, 1, 2, 8]
def baseStart_366965 : Nat := 118140960795 + 366965 * 2 ^ 59
def prefixEnd_366965 : Nat := 4983230072969 + 3 ^ 40 * 366965 * 2
def baseEnd_366965 : Nat := 12406875942535768325917

theorem tailTrace_366965 : CollatzResearch.WordTrace tailWord_366965 prefixEnd_366965 12406875942535768325917 := by
  unfold tailWord_366965
  simp only [CollatzResearch.WordTrace]
  refine ⟨13384313115555952477486349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8922875410370634984990899 13384313115555952477486349)
  ·
    refine ⟨5019117418333482179057381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13384313115555952477486349 5019117418333482179057381)
    ·
      refine ⟨941084515937527908573259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5019117418333482179057381 941084515937527908573259)
      ·
        refine ⟨1411626773906291862859889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941084515937527908573259 1411626773906291862859889)
        ·
          refine ⟨1058720080429718897144917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411626773906291862859889 1058720080429718897144917)
          ·
            refine ⟨12406875942535768325917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1058720080429718897144917 12406875942535768325917)
            ·
              rfl

theorem cell19_366965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 8].length) (baseStart_366965 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366965 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366965 prefixEnd_366965 := by exact prefixLift 366965
  have htrace : WordTrace (prefixWord ++ tailWord_366965) baseStart_366965 baseEnd_366965 := by
    simpa [prefixWord, tailWord_366965, baseEnd_366965] using wordTrace_append hprefix tailTrace_366965
  have hstable : (prefixWord ++ tailWord_366965).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366965).length < 2 ^ (prefixWord ++ tailWord_366965).sum := by decide
  have hdescent : baseEnd_366965 < baseStart_366965 := by decide
  rcases family_descends (prefixWord ++ tailWord_366965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366978 : List Nat := [3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_366978 : Nat := 118140960795 + 366978 * 2 ^ 59
def prefixEnd_366978 : Nat := 4983230072969 + 3 ^ 40 * 366978 * 2
def baseEnd_366978 : Nat := 111665839185641736644329

theorem tailTrace_366978 : CollatzResearch.WordTrace tailWord_366978 prefixEnd_366978 111665839185641736644329 := by
  unfold tailWord_366978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346196816127213924427397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8923191509672570465139725 3346196816127213924427397)
  ·
    refine ⟨627411903023852610830137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3346196816127213924427397 627411903023852610830137)
    ·
      refine ⟨470558927267889458122603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 627411903023852610830137 470558927267889458122603)
      ·
        refine ⟨705838390901834187183905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470558927267889458122603 705838390901834187183905)
        ·
          refine ⟨529378793176375640387929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705838390901834187183905 529378793176375640387929)
          ·
            refine ⟨397034094882281730290947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529378793176375640387929 397034094882281730290947)
            ·
              refine ⟨595551142323422595436421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397034094882281730290947 595551142323422595436421)
              ·
                refine ⟨111665839185641736644329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595551142323422595436421 111665839185641736644329)
                ·
                  rfl

theorem cell19_366978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_366978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_366978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_366978 prefixEnd_366978 := by exact prefixLift 366978
  have htrace : WordTrace (prefixWord ++ tailWord_366978) baseStart_366978 baseEnd_366978 := by
    simpa [prefixWord, tailWord_366978, baseEnd_366978] using wordTrace_append hprefix tailTrace_366978
  have hstable : (prefixWord ++ tailWord_366978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366978).length < 2 ^ (prefixWord ++ tailWord_366978).sum := by decide
  have hdescent : baseEnd_366978 < baseStart_366978 := by decide
  rcases family_descends (prefixWord ++ tailWord_366978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367043 : List Nat := [1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_367043 : Nat := 118140960795 + 367043 * 2 ^ 59
def prefixEnd_367043 : Nat := 4983230072969 + 3 ^ 40 * 367043 * 2
def baseEnd_367043 : Nat := 111685617699740845199707

theorem tailTrace_367043 : CollatzResearch.WordTrace tailWord_367043 prefixEnd_367043 111685617699740845199707 := by
  unfold tailWord_367043
  simp only [CollatzResearch.WordTrace]
  refine ⟨13387158009273371798825783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8924772006182247865883855 13387158009273371798825783)
  ·
    refine ⟨20080737013910057698238675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13387158009273371798825783 20080737013910057698238675)
    ·
      refine ⟨30121105520865086547358013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20080737013910057698238675 30121105520865086547358013)
      ·
        refine ⟨11295414570324407455259255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30121105520865086547358013 11295414570324407455259255)
        ·
          refine ⟨16943121855486611182888883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11295414570324407455259255 16943121855486611182888883)
          ·
            refine ⟨25414682783229916774333325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16943121855486611182888883 25414682783229916774333325)
            ·
              refine ⟨9530506043711218790374997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25414682783229916774333325 9530506043711218790374997)
              ·
                refine ⟨111685617699740845199707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9530506043711218790374997 111685617699740845199707)
                ·
                  rfl

theorem cell19_367043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_367043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367043 prefixEnd_367043 := by exact prefixLift 367043
  have htrace : WordTrace (prefixWord ++ tailWord_367043) baseStart_367043 baseEnd_367043 := by
    simpa [prefixWord, tailWord_367043, baseEnd_367043] using wordTrace_append hprefix tailTrace_367043
  have hstable : (prefixWord ++ tailWord_367043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367043).length < 2 ^ (prefixWord ++ tailWord_367043).sum := by decide
  have hdescent : baseEnd_367043 < baseStart_367043 := by decide
  rcases family_descends (prefixWord ++ tailWord_367043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367077 : List Nat := [1, 3, 1, 5, 2, 2, 5]
def baseStart_367077 : Nat := 118140960795 + 367077 * 2 ^ 59
def prefixEnd_367077 : Nat := 4983230072969 + 3 ^ 40 * 367077 * 2
def baseEnd_367077 : Nat := 37231987794679613481353

theorem tailTrace_367077 : CollatzResearch.WordTrace tailWord_367077 prefixEnd_367077 37231987794679613481353 := by
  unfold tailWord_367077
  simp only [CollatzResearch.WordTrace]
  refine ⟨13388398091150195605563485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8925598727433463737042323 13388398091150195605563485)
  ·
    refine ⟨5020649284181323352086307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13388398091150195605563485 5020649284181323352086307)
    ·
      refine ⟨7530973926271985028129461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5020649284181323352086307 7530973926271985028129461)
      ·
        refine ⟨706028805587998596387137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7530973926271985028129461 706028805587998596387137)
        ·
          refine ⟨529521604190998947290353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706028805587998596387137 529521604190998947290353)
          ·
            refine ⟨397141203143249210467765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529521604190998947290353 397141203143249210467765)
            ·
              refine ⟨37231987794679613481353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 397141203143249210467765 37231987794679613481353)
              ·
                rfl

theorem cell19_367077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_367077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367077 prefixEnd_367077 := by exact prefixLift 367077
  have htrace : WordTrace (prefixWord ++ tailWord_367077) baseStart_367077 baseEnd_367077 := by
    simpa [prefixWord, tailWord_367077, baseEnd_367077] using wordTrace_append hprefix tailTrace_367077
  have hstable : (prefixWord ++ tailWord_367077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367077).length < 2 ^ (prefixWord ++ tailWord_367077).sum := by decide
  have hdescent : baseEnd_367077 < baseStart_367077 := by decide
  rcases family_descends (prefixWord ++ tailWord_367077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367134 : List Nat := [4, 3, 3, 9]
def baseStart_367134 : Nat := 118140960795 + 367134 * 2 ^ 59
def prefixEnd_367134 : Nat := 4983230072969 + 3 ^ 40 * 367134 * 2
def baseEnd_367134 : Nat := 1379176637277525891077

theorem tailTrace_367134 : CollatzResearch.WordTrace tailWord_367134 prefixEnd_367134 1379176637277525891077 := by
  unfold tailWord_367134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673809631492961792548557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8926984701295796226925637 1673809631492961792548557)
  ·
    refine ⟨627678611809860672205709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1673809631492961792548557 627678611809860672205709)
    ·
      refine ⟨235379479428697752077141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 627678611809860672205709 235379479428697752077141)
      ·
        refine ⟨1379176637277525891077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 235379479428697752077141 1379176637277525891077)
        ·
          rfl

theorem cell19_367134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 9].length) (baseStart_367134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367134 prefixEnd_367134 := by exact prefixLift 367134
  have htrace : WordTrace (prefixWord ++ tailWord_367134) baseStart_367134 baseEnd_367134 := by
    simpa [prefixWord, tailWord_367134, baseEnd_367134] using wordTrace_append hprefix tailTrace_367134
  have hstable : (prefixWord ++ tailWord_367134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367134).length < 2 ^ (prefixWord ++ tailWord_367134).sum := by decide
  have hdescent : baseEnd_367134 < baseStart_367134 := by decide
  rcases family_descends (prefixWord ++ tailWord_367134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367136 : List Nat := [2, 1, 1, 6, 2, 7]
def baseStart_367136 : Nat := 118140960795 + 367136 * 2 ^ 59
def prefixEnd_367136 : Nat := 4983230072969 + 3 ^ 40 * 367136 * 2
def baseEnd_367136 : Nat := 12412657354349353903643

theorem tailTrace_367136 : CollatzResearch.WordTrace tailWord_367136 prefixEnd_367136 12412657354349353903643 := by
  unfold tailWord_367136
  simp only [CollatzResearch.WordTrace]
  refine ⟨6695274998968224340980631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8927033331957632454640841 6695274998968224340980631)
  ·
    refine ⟨10042912498452336511470947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6695274998968224340980631 10042912498452336511470947)
    ·
      refine ⟨15064368747678504767206421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10042912498452336511470947 15064368747678504767206421)
      ·
        refine ⟨706142285047429910962801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15064368747678504767206421 706142285047429910962801)
        ·
          refine ⟨529606713785572433222101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706142285047429910962801 529606713785572433222101)
          ·
            refine ⟨12412657354349353903643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 529606713785572433222101 12412657354349353903643)
            ·
              rfl

theorem cell19_367136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 7].length) (baseStart_367136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367136 prefixEnd_367136 := by exact prefixLift 367136
  have htrace : WordTrace (prefixWord ++ tailWord_367136) baseStart_367136 baseEnd_367136 := by
    simpa [prefixWord, tailWord_367136, baseEnd_367136] using wordTrace_append hprefix tailTrace_367136
  have hstable : (prefixWord ++ tailWord_367136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367136).length < 2 ^ (prefixWord ++ tailWord_367136).sum := by decide
  have hdescent : baseEnd_367136 < baseStart_367136 := by decide
  rcases family_descends (prefixWord ++ tailWord_367136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367176 : List Nat := [2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_367176 : Nat := 118140960795 + 367176 * 2 ^ 59
def prefixEnd_367176 : Nat := 4983230072969 + 3 ^ 40 * 367176 * 2
def baseEnd_367176 : Nat := 111726087582435944243789

theorem tailTrace_367176 : CollatzResearch.WordTrace tailWord_367176 prefixEnd_367176 111726087582435944243789 := by
  unfold tailWord_367176
  simp only [CollatzResearch.WordTrace]
  refine ⟨6696004458895767756708691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8928005945194357008944921 6696004458895767756708691)
  ·
    refine ⟨10044006688343651635063037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6696004458895767756708691 10044006688343651635063037)
    ·
      refine ⟨3766502508128869363148639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10044006688343651635063037 3766502508128869363148639)
      ·
        refine ⟨5649753762193304044722959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3766502508128869363148639 5649753762193304044722959)
        ·
          refine ⟨8474630643289956067084439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5649753762193304044722959 8474630643289956067084439)
          ·
            refine ⟨12711945964934934100626659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474630643289956067084439 12711945964934934100626659)
            ·
              refine ⟨19067918947402401150939989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12711945964934934100626659 19067918947402401150939989)
              ·
                refine ⟨111726087582435944243789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19067918947402401150939989 111726087582435944243789)
                ·
                  rfl

theorem cell19_367176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_367176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367176 prefixEnd_367176 := by exact prefixLift 367176
  have htrace : WordTrace (prefixWord ++ tailWord_367176) baseStart_367176 baseEnd_367176 := by
    simpa [prefixWord, tailWord_367176, baseEnd_367176] using wordTrace_append hprefix tailTrace_367176
  have hstable : (prefixWord ++ tailWord_367176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367176).length < 2 ^ (prefixWord ++ tailWord_367176).sum := by decide
  have hdescent : baseEnd_367176 < baseStart_367176 := by decide
  rcases family_descends (prefixWord ++ tailWord_367176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367250 : List Nat := [3, 2, 3, 1, 2, 1, 7]
def baseStart_367250 : Nat := 118140960795 + 367250 * 2 ^ 59
def prefixEnd_367250 : Nat := 4983230072969 + 3 ^ 40 * 367250 * 2
def baseEnd_367250 : Nat := 37249534886675232866381

theorem tailTrace_367250 : CollatzResearch.WordTrace tailWord_367250 prefixEnd_367250 37249534886675232866381 := by
  unfold tailWord_367250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348676979880861537902801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8929805279682297434407469 3348676979880861537902801)
  ·
    refine ⟨2511507734910646153427101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3348676979880861537902801 2511507734910646153427101)
    ·
      refine ⟨941815400591492307535163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2511507734910646153427101 941815400591492307535163)
      ·
        refine ⟨1412723100887238461302745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941815400591492307535163 1412723100887238461302745)
        ·
          refine ⟨1059542325665428845977059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1412723100887238461302745 1059542325665428845977059)
          ·
            refine ⟨1589313488498143268965589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059542325665428845977059 1589313488498143268965589)
            ·
              refine ⟨37249534886675232866381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1589313488498143268965589 37249534886675232866381)
              ·
                rfl

theorem cell19_367250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_367250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367250 prefixEnd_367250 := by exact prefixLift 367250
  have htrace : WordTrace (prefixWord ++ tailWord_367250) baseStart_367250 baseEnd_367250 := by
    simpa [prefixWord, tailWord_367250, baseEnd_367250] using wordTrace_append hprefix tailTrace_367250
  have hstable : (prefixWord ++ tailWord_367250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367250).length < 2 ^ (prefixWord ++ tailWord_367250).sum := by decide
  have hdescent : baseEnd_367250 < baseStart_367250 := by decide
  rcases family_descends (prefixWord ++ tailWord_367250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367290 : List Nat := [3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_367290 : Nat := 118140960795 + 367290 * 2 ^ 59
def prefixEnd_367290 : Nat := 4983230072969 + 3 ^ 40 * 367290 * 2
def baseEnd_367290 : Nat := 111760776053317457710145

theorem tailTrace_367290 : CollatzResearch.WordTrace tailWord_367290 prefixEnd_367290 111760776053317457710145 := by
  unfold tailWord_367290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349041709844633245766831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8930777892919021988711549 3349041709844633245766831)
  ·
    refine ⟨5023562564766949868650247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3349041709844633245766831 5023562564766949868650247)
    ·
      refine ⟨7535343847150424802975371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5023562564766949868650247 7535343847150424802975371)
      ·
        refine ⟨11303015770725637204463057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7535343847150424802975371 11303015770725637204463057)
        ·
          refine ⟨8477261828044227903347293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11303015770725637204463057 8477261828044227903347293)
          ·
            refine ⟨3178973185516585463755235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8477261828044227903347293 3178973185516585463755235)
            ·
              refine ⟨4768459778274878195632853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178973185516585463755235 4768459778274878195632853)
              ·
                refine ⟨111760776053317457710145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4768459778274878195632853 111760776053317457710145)
                ·
                  rfl

theorem cell19_367290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_367290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367290 prefixEnd_367290 := by exact prefixLift 367290
  have htrace : WordTrace (prefixWord ++ tailWord_367290) baseStart_367290 baseEnd_367290 := by
    simpa [prefixWord, tailWord_367290, baseEnd_367290] using wordTrace_append hprefix tailTrace_367290
  have hstable : (prefixWord ++ tailWord_367290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367290).length < 2 ^ (prefixWord ++ tailWord_367290).sum := by decide
  have hdescent : baseEnd_367290 < baseStart_367290 := by decide
  rcases family_descends (prefixWord ++ tailWord_367290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367324 : List Nat := [2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_367324 : Nat := 118140960795 + 367324 * 2 ^ 59
def prefixEnd_367324 : Nat := 4983230072969 + 3 ^ 40 * 367324 * 2
def baseEnd_367324 : Nat := 111771121737615452954497

theorem tailTrace_367324 : CollatzResearch.WordTrace tailWord_367324 prefixEnd_367324 111771121737615452954497 := by
  unfold tailWord_367324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6698703460627678394902513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8931604614170237859870017 6698703460627678394902513)
  ·
    refine ⟨5024027595470758796176885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6698703460627678394902513 5024027595470758796176885)
    ·
      refine ⟨471002587075383637141583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5024027595470758796176885 471002587075383637141583)
      ·
        refine ⟨706503880613075455712375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471002587075383637141583 706503880613075455712375)
        ·
          refine ⟨1059755820919613183568563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706503880613075455712375 1059755820919613183568563)
          ·
            refine ⟨1589633731379419775352845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059755820919613183568563 1589633731379419775352845)
            ·
              refine ⟨596112649267282415757317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1589633731379419775352845 596112649267282415757317)
              ·
                refine ⟨111771121737615452954497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596112649267282415757317 111771121737615452954497)
                ·
                  rfl

theorem cell19_367324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_367324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367324 prefixEnd_367324 := by exact prefixLift 367324
  have htrace : WordTrace (prefixWord ++ tailWord_367324) baseStart_367324 baseEnd_367324 := by
    simpa [prefixWord, tailWord_367324, baseEnd_367324] using wordTrace_append hprefix tailTrace_367324
  have hstable : (prefixWord ++ tailWord_367324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367324).length < 2 ^ (prefixWord ++ tailWord_367324).sum := by decide
  have hdescent : baseEnd_367324 < baseStart_367324 := by decide
  rcases family_descends (prefixWord ++ tailWord_367324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367345 : List Nat := [1, 2, 2, 2, 2, 2, 5, 3]
def baseStart_367345 : Nat := 118140960795 + 367345 * 2 ^ 59
def prefixEnd_367345 : Nat := 4983230072969 + 3 ^ 40 * 367345 * 2
def baseEnd_367345 : Nat := 111777511719093626487773

theorem tailTrace_367345 : CollatzResearch.WordTrace tailWord_367345 prefixEnd_367345 111777511719093626487773 := by
  unfold tailWord_367345
  simp only [CollatzResearch.WordTrace]
  refine ⟨13398172854179277376319489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8932115236119518250879659 13398172854179277376319489)
  ·
    refine ⟨10048629640634458032239617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13398172854179277376319489 10048629640634458032239617)
    ·
      refine ⟨7536472230475843524179713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10048629640634458032239617 7536472230475843524179713)
      ·
        refine ⟨5652354172856882643134785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7536472230475843524179713 5652354172856882643134785)
        ·
          refine ⟨4239265629642661982351089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5652354172856882643134785 4239265629642661982351089)
          ·
            refine ⟨3179449222231996486763317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4239265629642661982351089 3179449222231996486763317)
            ·
              refine ⟨298073364584249670634061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3179449222231996486763317 298073364584249670634061)
              ·
                refine ⟨111777511719093626487773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298073364584249670634061 111777511719093626487773)
                ·
                  rfl

theorem cell19_367345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_367345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367345 prefixEnd_367345 := by exact prefixLift 367345
  have htrace : WordTrace (prefixWord ++ tailWord_367345) baseStart_367345 baseEnd_367345 := by
    simpa [prefixWord, tailWord_367345, baseEnd_367345] using wordTrace_append hprefix tailTrace_367345
  have hstable : (prefixWord ++ tailWord_367345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367345).length < 2 ^ (prefixWord ++ tailWord_367345).sum := by decide
  have hdescent : baseEnd_367345 < baseStart_367345 := by decide
  rcases family_descends (prefixWord ++ tailWord_367345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367404 : List Nat := [2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_367404 : Nat := 118140960795 + 367404 * 2 ^ 59
def prefixEnd_367404 : Nat := 4983230072969 + 3 ^ 40 * 367404 * 2
def baseEnd_367404 : Nat := 111795464524198971176501

theorem tailTrace_367404 : CollatzResearch.WordTrace tailWord_367404 prefixEnd_367404 111795464524198971176501 := by
  unfold tailWord_367404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6700162380482765226358633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8933549840643686968478177 6700162380482765226358633)
  ·
    refine ⟨5025121785362073919768975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6700162380482765226358633 5025121785362073919768975)
    ·
      refine ⟨7537682678043110879653463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5025121785362073919768975 7537682678043110879653463)
      ·
        refine ⟨11306524017064666319480195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7537682678043110879653463 11306524017064666319480195)
        ·
          refine ⟨16959786025596999479220293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11306524017064666319480195 16959786025596999479220293)
          ·
            refine ⟨3179959879799437402353805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16959786025596999479220293 3179959879799437402353805)
            ·
              refine ⟨1192484954924789025882677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3179959879799437402353805 1192484954924789025882677)
              ·
                refine ⟨111795464524198971176501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1192484954924789025882677 111795464524198971176501)
                ·
                  rfl

theorem cell19_367404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_367404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367404 prefixEnd_367404 := by exact prefixLift 367404
  have htrace : WordTrace (prefixWord ++ tailWord_367404) baseStart_367404 baseEnd_367404 := by
    simpa [prefixWord, tailWord_367404, baseEnd_367404] using wordTrace_append hprefix tailTrace_367404
  have hstable : (prefixWord ++ tailWord_367404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367404).length < 2 ^ (prefixWord ++ tailWord_367404).sum := by decide
  have hdescent : baseEnd_367404 < baseStart_367404 := by decide
  rcases family_descends (prefixWord ++ tailWord_367404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367423 : List Nat := [1, 1, 2, 2, 5, 1, 7]
def baseStart_367423 : Nat := 118140960795 + 367423 * 2 ^ 59
def prefixEnd_367423 : Nat := 4983230072969 + 3 ^ 40 * 367423 * 2
def baseEnd_367423 : Nat := 37267081978670852251409

theorem tailTrace_367423 : CollatzResearch.WordTrace tailWord_367423 prefixEnd_367423 37267081978670852251409 := by
  unfold tailWord_367423
  simp only [CollatzResearch.WordTrace]
  refine ⟨13401017747896696697658923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8934011831931131131772615 13401017747896696697658923)
  ·
    refine ⟨20101526621845045046488385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13401017747896696697658923 20101526621845045046488385)
    ·
      refine ⟨15076144966383783784866289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20101526621845045046488385 15076144966383783784866289)
      ·
        refine ⟨11307108724787837838649717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15076144966383783784866289 11307108724787837838649717)
        ·
          refine ⟨1060041442948859797373411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11307108724787837838649717 1060041442948859797373411)
          ·
            refine ⟨1590062164423289696060117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060041442948859797373411 1590062164423289696060117)
            ·
              refine ⟨37267081978670852251409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1590062164423289696060117 37267081978670852251409)
              ·
                rfl

theorem cell19_367423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_367423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367423 prefixEnd_367423 := by exact prefixLift 367423
  have htrace : WordTrace (prefixWord ++ tailWord_367423) baseStart_367423 baseEnd_367423 := by
    simpa [prefixWord, tailWord_367423, baseEnd_367423] using wordTrace_append hprefix tailTrace_367423
  have hstable : (prefixWord ++ tailWord_367423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367423).length < 2 ^ (prefixWord ++ tailWord_367423).sum := by decide
  have hdescent : baseEnd_367423 < baseStart_367423 := by decide
  rcases family_descends (prefixWord ++ tailWord_367423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367461 : List Nat := [1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_367461 : Nat := 118140960795 + 367461 * 2 ^ 59
def prefixEnd_367461 : Nat := 4983230072969 + 3 ^ 40 * 367461 * 2
def baseEnd_367461 : Nat := 111812808759639727909679

theorem tailTrace_367461 : CollatzResearch.WordTrace tailWord_367461 prefixEnd_367461 111812808759639727909679 := by
  unfold tailWord_367461
  simp only [CollatzResearch.WordTrace]
  refine ⟨13402403721759029187542237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8934935814506019458361491 13402403721759029187542237)
  ·
    refine ⟨5025901395659635945328339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13402403721759029187542237 5025901395659635945328339)
    ·
      refine ⟨7538852093489453917992509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5025901395659635945328339 7538852093489453917992509)
      ·
        refine ⟨2827069535058545219247191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7538852093489453917992509 2827069535058545219247191)
        ·
          refine ⟨4240604302587817828870787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827069535058545219247191 4240604302587817828870787)
          ·
            refine ⟨6360906453881726743306181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240604302587817828870787 6360906453881726743306181)
            ·
              refine ⟨1192669960102823764369909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6360906453881726743306181 1192669960102823764369909)
              ·
                refine ⟨111812808759639727909679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1192669960102823764369909 111812808759639727909679)
                ·
                  rfl

theorem cell19_367461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_367461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367461 prefixEnd_367461 := by exact prefixLift 367461
  have htrace : WordTrace (prefixWord ++ tailWord_367461) baseStart_367461 baseEnd_367461 := by
    simpa [prefixWord, tailWord_367461, baseEnd_367461] using wordTrace_append hprefix tailTrace_367461
  have hstable : (prefixWord ++ tailWord_367461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367461).length < 2 ^ (prefixWord ++ tailWord_367461).sum := by decide
  have hdescent : baseEnd_367461 < baseStart_367461 := by decide
  rcases family_descends (prefixWord ++ tailWord_367461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367478 : List Nat := [5, 1, 1, 3, 1, 8]
def baseStart_367478 : Nat := 118140960795 + 367478 * 2 ^ 59
def prefixEnd_367478 : Nat := 4983230072969 + 3 ^ 40 * 367478 * 2
def baseEnd_367478 : Nat := 12424220177976525059095

theorem tailTrace_367478 : CollatzResearch.WordTrace tailWord_367478 prefixEnd_367478 12424220177976525059095 := by
  unfold tailWord_367478
  simp only [CollatzResearch.WordTrace]
  refine ⟨837688985168590068181943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8935349175131627393940725 837688985168590068181943)
  ·
    refine ⟨1256533477752885102272915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 837688985168590068181943 1256533477752885102272915)
    ·
      refine ⟨1884800216629327653409373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256533477752885102272915 1884800216629327653409373)
      ·
        refine ⟨706800081235997870028515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1884800216629327653409373 706800081235997870028515)
        ·
          refine ⟨1060200121853996805042773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706800081235997870028515 1060200121853996805042773)
          ·
            refine ⟨12424220177976525059095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1060200121853996805042773 12424220177976525059095)
            ·
              rfl

theorem cell19_367478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 8].length) (baseStart_367478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367478 prefixEnd_367478 := by exact prefixLift 367478
  have htrace : WordTrace (prefixWord ++ tailWord_367478) baseStart_367478 baseEnd_367478 := by
    simpa [prefixWord, tailWord_367478, baseEnd_367478] using wordTrace_append hprefix tailTrace_367478
  have hstable : (prefixWord ++ tailWord_367478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367478).length < 2 ^ (prefixWord ++ tailWord_367478).sum := by decide
  have hdescent : baseEnd_367478 < baseStart_367478 := by decide
  rcases family_descends (prefixWord ++ tailWord_367478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367497 : List Nat := [1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_367497 : Nat := 118140960795 + 367497 * 2 ^ 59
def prefixEnd_367497 : Nat := 4983230072969 + 3 ^ 40 * 367497 * 2
def baseEnd_367497 : Nat := 111823763013602311109581

theorem tailTrace_367497 : CollatzResearch.WordTrace tailWord_367497 prefixEnd_367497 111823763013602311109581 := by
  unfold tailWord_367497
  simp only [CollatzResearch.WordTrace]
  refine ⟨13403716749628607335852745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8935811166419071557235163 13403716749628607335852745)
  ·
    refine ⟨10052787562221455501889559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13403716749628607335852745 10052787562221455501889559)
    ·
      refine ⟨15079181343332183252834339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10052787562221455501889559 15079181343332183252834339)
      ·
        refine ⟨22618772014998274879251509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15079181343332183252834339 22618772014998274879251509)
        ·
          refine ⟨2120509876406088269929829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22618772014998274879251509 2120509876406088269929829)
          ·
            refine ⟨397595601826141550611843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2120509876406088269929829 397595601826141550611843)
            ·
              refine ⟨596393402739212325917765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397595601826141550611843 596393402739212325917765)
              ·
                refine ⟨111823763013602311109581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596393402739212325917765 111823763013602311109581)
                ·
                  rfl

theorem cell19_367497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_367497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367497 prefixEnd_367497 := by exact prefixLift 367497
  have htrace : WordTrace (prefixWord ++ tailWord_367497) baseStart_367497 baseEnd_367497 := by
    simpa [prefixWord, tailWord_367497, baseEnd_367497] using wordTrace_append hprefix tailTrace_367497
  have hstable : (prefixWord ++ tailWord_367497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367497).length < 2 ^ (prefixWord ++ tailWord_367497).sum := by decide
  have hdescent : baseEnd_367497 < baseStart_367497 := by decide
  rcases family_descends (prefixWord ++ tailWord_367497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367499 : List Nat := [1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_367499 : Nat := 118140960795 + 367499 * 2 ^ 59
def prefixEnd_367499 : Nat := 4983230072969 + 3 ^ 40 * 367499 * 2
def baseEnd_367499 : Nat := 111824371583266899065131

theorem tailTrace_367499 : CollatzResearch.WordTrace tailWord_367499 prefixEnd_367499 111824371583266899065131 := by
  unfold tailWord_367499
  simp only [CollatzResearch.WordTrace]
  refine ⟨13403789695621361677425551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8935859797080907784950367 13403789695621361677425551)
  ·
    refine ⟨20105684543432042516138327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13403789695621361677425551 20105684543432042516138327)
    ·
      refine ⟨30158526815148063774207491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20105684543432042516138327 30158526815148063774207491)
      ·
        refine ⟨45237790222722095661311237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30158526815148063774207491 45237790222722095661311237)
        ·
          refine ⟨8482085666760392936495857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45237790222722095661311237 8482085666760392936495857)
          ·
            refine ⟨6361564250070294702371893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8482085666760392936495857 6361564250070294702371893)
            ·
              refine ⟨596396648444090128347365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6361564250070294702371893 596396648444090128347365)
              ·
                refine ⟨111824371583266899065131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596396648444090128347365 111824371583266899065131)
                ·
                  rfl

theorem cell19_367499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_367499 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367499 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367499 prefixEnd_367499 := by exact prefixLift 367499
  have htrace : WordTrace (prefixWord ++ tailWord_367499) baseStart_367499 baseEnd_367499 := by
    simpa [prefixWord, tailWord_367499, baseEnd_367499] using wordTrace_append hprefix tailTrace_367499
  have hstable : (prefixWord ++ tailWord_367499).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367499).length < 2 ^ (prefixWord ++ tailWord_367499).sum := by decide
  have hdescent : baseEnd_367499 < baseStart_367499 := by decide
  rcases family_descends (prefixWord ++ tailWord_367499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367510 : List Nat := [5, 3, 1, 1, 1, 2, 3, 3]
def baseStart_367510 : Nat := 118140960795 + 367510 * 2 ^ 59
def prefixEnd_367510 : Nat := 4983230072969 + 3 ^ 40 * 367510 * 2
def baseEnd_367510 : Nat := 111827718716422132820657

theorem tailTrace_367510 : CollatzResearch.WordTrace tailWord_367510 prefixEnd_367510 111827718716422132820657 := by
  unfold tailWord_367510
  simp only [CollatzResearch.WordTrace]
  refine ⟨837761931161344409754749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8936127265721007037383989 837761931161344409754749)
  ·
    refine ⟨314160724185504153658031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 837761931161344409754749 314160724185504153658031)
    ·
      refine ⟨471241086278256230487047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314160724185504153658031 471241086278256230487047)
      ·
        refine ⟨706861629417384345730571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471241086278256230487047 706861629417384345730571)
        ·
          refine ⟨1060292444126076518595857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706861629417384345730571 1060292444126076518595857)
          ·
            refine ⟨795219333094557388946893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060292444126076518595857 795219333094557388946893)
            ·
              refine ⟨298207249910459020855085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795219333094557388946893 298207249910459020855085)
              ·
                refine ⟨111827718716422132820657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298207249910459020855085 111827718716422132820657)
                ·
                  rfl

theorem cell19_367510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_367510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367510 prefixEnd_367510 := by exact prefixLift 367510
  have htrace : WordTrace (prefixWord ++ tailWord_367510) baseStart_367510 baseEnd_367510 := by
    simpa [prefixWord, tailWord_367510, baseEnd_367510] using wordTrace_append hprefix tailTrace_367510
  have hstable : (prefixWord ++ tailWord_367510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367510).length < 2 ^ (prefixWord ++ tailWord_367510).sum := by decide
  have hdescent : baseEnd_367510 < baseStart_367510 := by decide
  rcases family_descends (prefixWord ++ tailWord_367510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367514 : List Nat := [3, 1, 1, 4, 3, 1, 3, 3]
def baseStart_367514 : Nat := 118140960795 + 367514 * 2 ^ 59
def prefixEnd_367514 : Nat := 4983230072969 + 3 ^ 40 * 367514 * 2
def baseEnd_367514 : Nat := 111828935855751308731757

theorem tailTrace_367514 : CollatzResearch.WordTrace tailWord_367514 prefixEnd_367514 111828935855751308731757 := by
  unfold tailWord_367514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351084197641754809805399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8936224527044679492814397 3351084197641754809805399)
  ·
    refine ⟨5026626296462632214708099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3351084197641754809805399 5026626296462632214708099)
    ·
      refine ⟨7539939444693948322062149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5026626296462632214708099 7539939444693948322062149)
      ·
        refine ⟨1413738645880115310386653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7539939444693948322062149 1413738645880115310386653)
        ·
          refine ⟨530151992205043241394995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1413738645880115310386653 530151992205043241394995)
          ·
            refine ⟨795227988307564862092493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530151992205043241394995 795227988307564862092493)
            ·
              refine ⟨298210495615336823284685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795227988307564862092493 298210495615336823284685)
              ·
                refine ⟨111828935855751308731757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298210495615336823284685 111828935855751308731757)
                ·
                  rfl

theorem cell19_367514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_367514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367514 prefixEnd_367514 := by exact prefixLift 367514
  have htrace : WordTrace (prefixWord ++ tailWord_367514) baseStart_367514 baseEnd_367514 := by
    simpa [prefixWord, tailWord_367514, baseEnd_367514] using wordTrace_append hprefix tailTrace_367514
  have hstable : (prefixWord ++ tailWord_367514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367514).length < 2 ^ (prefixWord ++ tailWord_367514).sum := by decide
  have hdescent : baseEnd_367514 < baseStart_367514 := by decide
  rcases family_descends (prefixWord ++ tailWord_367514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367533 : List Nat := [1, 5, 2, 3, 1, 1, 6]
def baseStart_367533 : Nat := 118140960795 + 367533 * 2 ^ 59
def prefixEnd_367533 : Nat := 4983230072969 + 3 ^ 40 * 367533 * 2
def baseEnd_367533 : Nat := 37278239089188298103161

theorem tailTrace_367533 : CollatzResearch.WordTrace tailWord_367533 prefixEnd_367533 37278239089188298103161 := by
  unfold tailWord_367533
  simp only [CollatzResearch.WordTrace]
  refine ⟨13405029777498185484163253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8936686518332123656108835 13405029777498185484163253)
  ·
    refine ⟨1256721541640454889140305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13405029777498185484163253 1256721541640454889140305)
    ·
      refine ⟨942541156230341166855229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1256721541640454889140305 942541156230341166855229)
      ·
        refine ⟨353452933586377937570711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 942541156230341166855229 353452933586377937570711)
        ·
          refine ⟨530179400379566906356067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353452933586377937570711 530179400379566906356067)
          ·
            refine ⟨795269100569350359534101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530179400379566906356067 795269100569350359534101)
            ·
              refine ⟨37278239089188298103161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 795269100569350359534101 37278239089188298103161)
              ·
                rfl

theorem cell19_367533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_367533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367533 prefixEnd_367533 := by exact prefixLift 367533
  have htrace : WordTrace (prefixWord ++ tailWord_367533) baseStart_367533 baseEnd_367533 := by
    simpa [prefixWord, tailWord_367533, baseEnd_367533] using wordTrace_append hprefix tailTrace_367533
  have hstable : (prefixWord ++ tailWord_367533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367533).length < 2 ^ (prefixWord ++ tailWord_367533).sum := by decide
  have hdescent : baseEnd_367533 < baseStart_367533 := by decide
  rcases family_descends (prefixWord ++ tailWord_367533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367565 : List Nat := [1, 6, 3, 1, 1, 2, 2, 3]
def baseStart_367565 : Nat := 118140960795 + 367565 * 2 ^ 59
def prefixEnd_367565 : Nat := 4983230072969 + 3 ^ 40 * 367565 * 2
def baseEnd_367565 : Nat := 111844454382198301598285

theorem tailTrace_367565 : CollatzResearch.WordTrace tailWord_367565 prefixEnd_367565 111844454382198301598285 := by
  unfold tailWord_367565
  simp only [CollatzResearch.WordTrace]
  refine ⟨13406196913382254949328149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8937464608921503299552099 13406196913382254949328149)
  ·
    refine ⟨628415480314793200749757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13406196913382254949328149 628415480314793200749757)
    ·
      refine ⟨235655805118047450281159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 628415480314793200749757 235655805118047450281159)
      ·
        refine ⟨353483707677071175421739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235655805118047450281159 353483707677071175421739)
        ·
          refine ⟨530225561515606763132609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353483707677071175421739 530225561515606763132609)
          ·
            refine ⟨397669171136705072349457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530225561515606763132609 397669171136705072349457)
            ·
              refine ⟨298251878352528804262093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397669171136705072349457 298251878352528804262093)
              ·
                refine ⟨111844454382198301598285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298251878352528804262093 111844454382198301598285)
                ·
                  rfl

theorem cell19_367565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 3].length) (baseStart_367565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367565 prefixEnd_367565 := by exact prefixLift 367565
  have htrace : WordTrace (prefixWord ++ tailWord_367565) baseStart_367565 baseEnd_367565 := by
    simpa [prefixWord, tailWord_367565, baseEnd_367565] using wordTrace_append hprefix tailTrace_367565
  have hstable : (prefixWord ++ tailWord_367565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367565).length < 2 ^ (prefixWord ++ tailWord_367565).sum := by decide
  have hdescent : baseEnd_367565 < baseStart_367565 := by decide
  rcases family_descends (prefixWord ++ tailWord_367565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367573 : List Nat := [1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_367573 : Nat := 118140960795 + 367573 * 2 ^ 59
def prefixEnd_367573 : Nat := 4983230072969 + 3 ^ 40 * 367573 * 2
def baseEnd_367573 : Nat := 111846888660856653420485

theorem tailTrace_367573 : CollatzResearch.WordTrace tailWord_367573 prefixEnd_367573 111846888660856653420485 := by
  unfold tailWord_367573
  simp only [CollatzResearch.WordTrace]
  refine ⟨13406488697353272315619373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8937659131568848210412915 13406488697353272315619373)
  ·
    refine ⟨5027433261507477118357265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13406488697353272315619373 5027433261507477118357265)
    ·
      refine ⟨3770574946130607838767949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5027433261507477118357265 3770574946130607838767949)
      ·
        refine ⟨1413965604798977939537981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3770574946130607838767949 1413965604798977939537981)
        ·
          refine ⟨530237101799616727326743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1413965604798977939537981 530237101799616727326743)
          ·
            refine ⟨795355652699425090990115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530237101799616727326743 795355652699425090990115)
            ·
              refine ⟨1193033479049137636485173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795355652699425090990115 1193033479049137636485173)
              ·
                refine ⟨111846888660856653420485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1193033479049137636485173 111846888660856653420485)
                ·
                  rfl

theorem cell19_367573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_367573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367573 prefixEnd_367573 := by exact prefixLift 367573
  have htrace : WordTrace (prefixWord ++ tailWord_367573) baseStart_367573 baseEnd_367573 := by
    simpa [prefixWord, tailWord_367573, baseEnd_367573] using wordTrace_append hprefix tailTrace_367573
  have hstable : (prefixWord ++ tailWord_367573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367573).length < 2 ^ (prefixWord ++ tailWord_367573).sum := by decide
  have hdescent : baseEnd_367573 < baseStart_367573 := by decide
  rcases family_descends (prefixWord ++ tailWord_367573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367594 : List Nat := [3, 1, 3, 1, 2, 2, 7]
def baseStart_367594 : Nat := 118140960795 + 367594 * 2 ^ 59
def prefixEnd_367594 : Nat := 4983230072969 + 3 ^ 40 * 367594 * 2
def baseEnd_367594 : Nat := 37284426214111608984587

theorem tailTrace_367594 : CollatzResearch.WordTrace tailWord_367594 prefixEnd_367594 37284426214111608984587 := by
  unfold tailWord_367594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351813657569298225533459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8938169753518128601422557 3351813657569298225533459)
  ·
    refine ⟨5027720486353947338300189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3351813657569298225533459 5027720486353947338300189)
    ·
      refine ⟨1885395182382730251862571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5027720486353947338300189 1885395182382730251862571)
      ·
        refine ⟨2828092773574095377793857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885395182382730251862571 2828092773574095377793857)
        ·
          refine ⟨2121069580180571533345393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2828092773574095377793857 2121069580180571533345393)
          ·
            refine ⟨1590802185135428650009045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2121069580180571533345393 1590802185135428650009045)
            ·
              refine ⟨37284426214111608984587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1590802185135428650009045 37284426214111608984587)
              ·
                rfl

theorem cell19_367594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_367594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367594 prefixEnd_367594 := by exact prefixLift 367594
  have htrace : WordTrace (prefixWord ++ tailWord_367594) baseStart_367594 baseEnd_367594 := by
    simpa [prefixWord, tailWord_367594, baseEnd_367594] using wordTrace_append hprefix tailTrace_367594
  have hstable : (prefixWord ++ tailWord_367594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367594).length < 2 ^ (prefixWord ++ tailWord_367594).sum := by decide
  have hdescent : baseEnd_367594 < baseStart_367594 := by decide
  rcases family_descends (prefixWord ++ tailWord_367594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367687 : List Nat := [1, 1, 4, 1, 3, 3, 3, 3]
def baseStart_367687 : Nat := 118140960795 + 367687 * 2 ^ 59
def prefixEnd_367687 : Nat := 4983230072969 + 3 ^ 40 * 367687 * 2
def baseEnd_367687 : Nat := 111881577131738166886841

theorem tailTrace_367687 : CollatzResearch.WordTrace tailWord_367687 prefixEnd_367687 111881577131738166886841 := by
  unfold tailWord_367687
  simp only [CollatzResearch.WordTrace]
  refine ⟨13410646618940269785269315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8940431079293513190179543 13410646618940269785269315)
  ·
    refine ⟨20115969928410404677903973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13410646618940269785269315 20115969928410404677903973)
    ·
      refine ⟨3771744361576950877106995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20115969928410404677903973 3771744361576950877106995)
      ·
        refine ⟨5657616542365426315660493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771744361576950877106995 5657616542365426315660493)
        ·
          refine ⟨2121606203387034868372685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5657616542365426315660493 2121606203387034868372685)
          ·
            refine ⟨795602326270138075639757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2121606203387034868372685 795602326270138075639757)
            ·
              refine ⟨298350872351301778364909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795602326270138075639757 298350872351301778364909)
              ·
                refine ⟨111881577131738166886841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298350872351301778364909 111881577131738166886841)
                ·
                  rfl

theorem cell19_367687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_367687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367687 prefixEnd_367687 := by exact prefixLift 367687
  have htrace : WordTrace (prefixWord ++ tailWord_367687) baseStart_367687 baseEnd_367687 := by
    simpa [prefixWord, tailWord_367687, baseEnd_367687] using wordTrace_append hprefix tailTrace_367687
  have hstable : (prefixWord ++ tailWord_367687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367687).length < 2 ^ (prefixWord ++ tailWord_367687).sum := by decide
  have hdescent : baseEnd_367687 < baseStart_367687 := by decide
  rcases family_descends (prefixWord ++ tailWord_367687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367708 : List Nat := [2, 2, 4, 1, 1, 1, 8]
def baseStart_367708 : Nat := 118140960795 + 367708 * 2 ^ 59
def prefixEnd_367708 : Nat := 4983230072969 + 3 ^ 40 * 367708 * 2
def baseEnd_367708 : Nat := 37295989037738780140039

theorem tailTrace_367708 : CollatzResearch.WordTrace tailWord_367708 prefixEnd_367708 37295989037738780140039 := by
  unfold tailWord_367708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6705706275932095185891889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8940941701242793581189185 6705706275932095185891889)
  ·
    refine ⟨5029279706949071389418917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6705706275932095185891889 5029279706949071389418917)
    ·
      refine ⟨942989945052950885516047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5029279706949071389418917 942989945052950885516047)
      ·
        refine ⟨1414484917579426328274071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942989945052950885516047 1414484917579426328274071)
        ·
          refine ⟨2121727376369139492411107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414484917579426328274071 2121727376369139492411107)
          ·
            refine ⟨3182591064553709238616661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121727376369139492411107 3182591064553709238616661)
            ·
              refine ⟨37295989037738780140039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3182591064553709238616661 37295989037738780140039)
              ·
                rfl

theorem cell19_367708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_367708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367708 prefixEnd_367708 := by exact prefixLift 367708
  have htrace : WordTrace (prefixWord ++ tailWord_367708) baseStart_367708 baseEnd_367708 := by
    simpa [prefixWord, tailWord_367708, baseEnd_367708] using wordTrace_append hprefix tailTrace_367708
  have hstable : (prefixWord ++ tailWord_367708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367708).length < 2 ^ (prefixWord ++ tailWord_367708).sum := by decide
  have hdescent : baseEnd_367708 < baseStart_367708 := by decide
  rcases family_descends (prefixWord ++ tailWord_367708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367822 : List Nat := [4, 1, 1, 1, 5, 7]
def baseStart_367822 : Nat := 118140960795 + 367822 * 2 ^ 59
def prefixEnd_367822 : Nat := 4983230072969 + 3 ^ 40 * 367822 * 2
def baseEnd_367822 : Nat := 12435850620455317098497

theorem tailTrace_367822 : CollatzResearch.WordTrace tailWord_367822 prefixEnd_367822 12435850620455317098497 := by
  unfold tailWord_367822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676946309181398480179215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8943713648967458560955813 1676946309181398480179215)
  ·
    refine ⟨2515419463772097720268823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1676946309181398480179215 2515419463772097720268823)
    ·
      refine ⟨3773129195658146580403235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2515419463772097720268823 3773129195658146580403235)
      ·
        refine ⟨5659693793487219870604853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773129195658146580403235 5659693793487219870604853)
        ·
          refine ⟨530596293139426862869205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5659693793487219870604853 530596293139426862869205)
          ·
            refine ⟨12435850620455317098497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 530596293139426862869205 12435850620455317098497)
            ·
              rfl

theorem cell19_367822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 7].length) (baseStart_367822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367822 prefixEnd_367822 := by exact prefixLift 367822
  have htrace : WordTrace (prefixWord ++ tailWord_367822) baseStart_367822 baseEnd_367822 := by
    simpa [prefixWord, tailWord_367822, baseEnd_367822] using wordTrace_append hprefix tailTrace_367822
  have hstable : (prefixWord ++ tailWord_367822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367822).length < 2 ^ (prefixWord ++ tailWord_367822).sum := by decide
  have hdescent : baseEnd_367822 < baseStart_367822 := by decide
  rcases family_descends (prefixWord ++ tailWord_367822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367837 : List Nat := [1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_367837 : Nat := 118140960795 + 367837 * 2 ^ 59
def prefixEnd_367837 : Nat := 4983230072969 + 3 ^ 40 * 367837 * 2
def baseEnd_367837 : Nat := 111927219856582263553099

theorem tailTrace_367837 : CollatzResearch.WordTrace tailWord_367837 prefixEnd_367837 111927219856582263553099 := by
  unfold tailWord_367837
  simp only [CollatzResearch.WordTrace]
  refine ⟨13416117568396845403229765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8944078378931230268819843 13416117568396845403229765)
  ·
    refine ⟨2515522044074408513105581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13416117568396845403229765 2515522044074408513105581)
    ·
      refine ⟨943320766527903192414593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2515522044074408513105581 943320766527903192414593)
      ·
        refine ⟨707490574895927394310945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 943320766527903192414593 707490574895927394310945)
        ·
          refine ⟨530617931171945545733209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707490574895927394310945 530617931171945545733209)
          ·
            refine ⟨397963448378959159299907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530617931171945545733209 397963448378959159299907)
            ·
              refine ⟨596945172568438738949861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397963448378959159299907 596945172568438738949861)
              ·
                refine ⟨111927219856582263553099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596945172568438738949861 111927219856582263553099)
                ·
                  rfl

theorem cell19_367837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_367837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367837 prefixEnd_367837 := by exact prefixLift 367837
  have htrace : WordTrace (prefixWord ++ tailWord_367837) baseStart_367837 baseEnd_367837 := by
    simpa [prefixWord, tailWord_367837, baseEnd_367837] using wordTrace_append hprefix tailTrace_367837
  have hstable : (prefixWord ++ tailWord_367837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367837).length < 2 ^ (prefixWord ++ tailWord_367837).sum := by decide
  have hdescent : baseEnd_367837 < baseStart_367837 := by decide
  rcases family_descends (prefixWord ++ tailWord_367837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367841 : List Nat := [1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_367841 : Nat := 118140960795 + 367841 * 2 ^ 59
def prefixEnd_367841 : Nat := 4983230072969 + 3 ^ 40 * 367841 * 2
def baseEnd_367841 : Nat := 111928436995911439464199

theorem tailTrace_367841 : CollatzResearch.WordTrace tailWord_367841 prefixEnd_367841 111928436995911439464199 := by
  unfold tailWord_367841
  simp only [CollatzResearch.WordTrace]
  refine ⟨13416263460382354086375377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8944175640254902724250251 13416263460382354086375377)
  ·
    refine ⟨10062197595286765564781533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13416263460382354086375377 10062197595286765564781533)
    ·
      refine ⟨3773324098232537086793075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10062197595286765564781533 3773324098232537086793075)
      ·
        refine ⟨5659986147348805630189613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773324098232537086793075 5659986147348805630189613)
        ·
          refine ⟨2122494805255802111321105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5659986147348805630189613 2122494805255802111321105)
          ·
            refine ⟨1591871103941851583490829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2122494805255802111321105 1591871103941851583490829)
            ·
              refine ⟨596951663978194343809061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1591871103941851583490829 596951663978194343809061)
              ·
                refine ⟨111928436995911439464199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596951663978194343809061 111928436995911439464199)
                ·
                  rfl

theorem cell19_367841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_367841 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367841 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367841 prefixEnd_367841 := by exact prefixLift 367841
  have htrace : WordTrace (prefixWord ++ tailWord_367841) baseStart_367841 baseEnd_367841 := by
    simpa [prefixWord, tailWord_367841, baseEnd_367841] using wordTrace_append hprefix tailTrace_367841
  have hstable : (prefixWord ++ tailWord_367841).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367841).length < 2 ^ (prefixWord ++ tailWord_367841).sum := by decide
  have hdescent : baseEnd_367841 < baseStart_367841 := by decide
  rcases family_descends (prefixWord ++ tailWord_367841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367881 : List Nat := [1, 2, 1, 1, 3, 3, 8]
def baseStart_367881 : Nat := 118140960795 + 367881 * 2 ^ 59
def prefixEnd_367881 : Nat := 4983230072969 + 3 ^ 40 * 367881 * 2
def baseEnd_367881 : Nat := 37313536129734399525067

theorem tailTrace_367881 : CollatzResearch.WordTrace tailWord_367881 prefixEnd_367881 37313536129734399525067 := by
  unfold tailWord_367881
  simp only [CollatzResearch.WordTrace]
  refine ⟨13417722380237440917831497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8945148253491627278554331 13417722380237440917831497)
  ·
    refine ⟨10063291785178080688373623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13417722380237440917831497 10063291785178080688373623)
    ·
      refine ⟨15094937677767121032560435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10063291785178080688373623 15094937677767121032560435)
      ·
        refine ⟨22642406516650681548840653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15094937677767121032560435 22642406516650681548840653)
        ·
          refine ⟨8490902443744005580815245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22642406516650681548840653 8490902443744005580815245)
          ·
            refine ⟨3184088416404002092805717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8490902443744005580815245 3184088416404002092805717)
            ·
              refine ⟨37313536129734399525067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3184088416404002092805717 37313536129734399525067)
              ·
                rfl

theorem cell19_367881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_367881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_367881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_367881 prefixEnd_367881 := by exact prefixLift 367881
  have htrace : WordTrace (prefixWord ++ tailWord_367881) baseStart_367881 baseEnd_367881 := by
    simpa [prefixWord, tailWord_367881, baseEnd_367881] using wordTrace_append hprefix tailTrace_367881
  have hstable : (prefixWord ++ tailWord_367881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367881).length < 2 ^ (prefixWord ++ tailWord_367881).sum := by decide
  have hdescent : baseEnd_367881 < baseStart_367881 := by decide
  rcases family_descends (prefixWord ++ tailWord_367881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368029 : List Nat := [1, 4, 2, 1, 3, 2, 3, 3]
def baseStart_368029 : Nat := 118140960795 + 368029 * 2 ^ 59
def prefixEnd_368029 : Nat := 4983230072969 + 3 ^ 40 * 368029 * 2
def baseEnd_368029 : Nat := 111985642544382707285909

theorem tailTrace_368029 : CollatzResearch.WordTrace tailWord_368029 prefixEnd_368029 111985642544382707285909 := by
  unfold tailWord_368029
  simp only [CollatzResearch.WordTrace]
  refine ⟨13423120383701262194219141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8948746922467508129479427 13423120383701262194219141)
  ·
    refine ⟨2516835071943986661416089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13423120383701262194219141 2516835071943986661416089)
    ·
      refine ⟨1887626303957989996062067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2516835071943986661416089 1887626303957989996062067)
      ·
        refine ⟨2831439455936984994093101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887626303957989996062067 2831439455936984994093101)
        ·
          refine ⟨1061789795976369372784913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2831439455936984994093101 1061789795976369372784913)
          ·
            refine ⟨796342346982277029588685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1061789795976369372784913 796342346982277029588685)
            ·
              refine ⟨298628380118353886095757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 796342346982277029588685 298628380118353886095757)
              ·
                refine ⟨111985642544382707285909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298628380118353886095757 111985642544382707285909)
                ·
                  rfl

theorem cell19_368029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_368029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368029 prefixEnd_368029 := by exact prefixLift 368029
  have htrace : WordTrace (prefixWord ++ tailWord_368029) baseStart_368029 baseEnd_368029 := by
    simpa [prefixWord, tailWord_368029, baseEnd_368029] using wordTrace_append hprefix tailTrace_368029
  have hstable : (prefixWord ++ tailWord_368029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368029).length < 2 ^ (prefixWord ++ tailWord_368029).sum := by decide
  have hdescent : baseEnd_368029 < baseStart_368029 := by decide
  rcases family_descends (prefixWord ++ tailWord_368029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368071 : List Nat := [1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_368071 : Nat := 118140960795 + 368071 * 2 ^ 59
def prefixEnd_368071 : Nat := 4983230072969 + 3 ^ 40 * 368071 * 2
def baseEnd_368071 : Nat := 111998422507339054352461

theorem tailTrace_368071 : CollatzResearch.WordTrace tailWord_368071 prefixEnd_368071 111998422507339054352461 := by
  unfold tailWord_368071
  simp only [CollatzResearch.WordTrace]
  refine ⟨13424652249549103367248067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8949768166366068911498711 13424652249549103367248067)
  ·
    refine ⟨20136978374323655050872101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13424652249549103367248067 20136978374323655050872101)
    ·
      refine ⟨3775683445185685322038519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20136978374323655050872101 3775683445185685322038519)
      ·
        refine ⟨5663525167778527983057779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775683445185685322038519 5663525167778527983057779)
        ·
          refine ⟨8495287751667791974586669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5663525167778527983057779 8495287751667791974586669)
          ·
            refine ⟨3185732906875421990470001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8495287751667791974586669 3185732906875421990470001)
            ·
              refine ⟨2389299680156566492852501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185732906875421990470001 2389299680156566492852501)
              ·
                refine ⟨111998422507339054352461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2389299680156566492852501 111998422507339054352461)
                ·
                  rfl

theorem cell19_368071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_368071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368071 prefixEnd_368071 := by exact prefixLift 368071
  have htrace : WordTrace (prefixWord ++ tailWord_368071) baseStart_368071 baseEnd_368071 := by
    simpa [prefixWord, tailWord_368071, baseEnd_368071] using wordTrace_append hprefix tailTrace_368071
  have hstable : (prefixWord ++ tailWord_368071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368071).length < 2 ^ (prefixWord ++ tailWord_368071).sum := by decide
  have hdescent : baseEnd_368071 < baseStart_368071 := by decide
  rcases family_descends (prefixWord ++ tailWord_368071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368084 : List Nat := [2, 4, 1, 2, 3, 2, 2, 3]
def baseStart_368084 : Nat := 118140960795 + 368084 * 2 ^ 59
def prefixEnd_368084 : Nat := 4983230072969 + 3 ^ 40 * 368084 * 2
def baseEnd_368084 : Nat := 112002378210158876063537

theorem tailTrace_368084 : CollatzResearch.WordTrace tailWord_368084 prefixEnd_368084 112002378210158876063537 := by
  unfold tailWord_368084
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712563199251003293735653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8950084265668004391647537 6712563199251003293735653)
  ·
    refine ⟨1258605599859563117575435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6712563199251003293735653 1258605599859563117575435)
    ·
      refine ⟨1887908399789344676363153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258605599859563117575435 1887908399789344676363153)
      ·
        refine ⟨1415931299842008507272365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1887908399789344676363153 1415931299842008507272365)
        ·
          refine ⟨530974237440753190227137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1415931299842008507272365 530974237440753190227137)
          ·
            refine ⟨398230678080564892670353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530974237440753190227137 398230678080564892670353)
            ·
              refine ⟨298673008560423669502765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398230678080564892670353 298673008560423669502765)
              ·
                refine ⟨112002378210158876063537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298673008560423669502765 112002378210158876063537)
                ·
                  rfl

theorem cell19_368084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_368084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368084 prefixEnd_368084 := by exact prefixLift 368084
  have htrace : WordTrace (prefixWord ++ tailWord_368084) baseStart_368084 baseEnd_368084 := by
    simpa [prefixWord, tailWord_368084, baseEnd_368084] using wordTrace_append hprefix tailTrace_368084
  have hstable : (prefixWord ++ tailWord_368084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368084).length < 2 ^ (prefixWord ++ tailWord_368084).sum := by decide
  have hdescent : baseEnd_368084 < baseStart_368084 := by decide
  rcases family_descends (prefixWord ++ tailWord_368084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368086 : List Nat := [5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_368086 : Nat := 118140960795 + 368086 * 2 ^ 59
def prefixEnd_368086 : Nat := 4983230072969 + 3 ^ 40 * 368086 * 2
def baseEnd_368086 : Nat := 112002986779823464019087

theorem tailTrace_368086 : CollatzResearch.WordTrace tailWord_368086 prefixEnd_368086 112002986779823464019087 := by
  unfold tailWord_368086
  simp only [CollatzResearch.WordTrace]
  refine ⟨839074959030922558065257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8950132896329840619362741 839074959030922558065257)
  ·
    refine ⟨629306219273191918548943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 839074959030922558065257 629306219273191918548943)
    ·
      refine ⟨943959328909787877823415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 629306219273191918548943 943959328909787877823415)
      ·
        refine ⟨1415938993364681816735123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943959328909787877823415 1415938993364681816735123)
        ·
          refine ⟨2123908490047022725102685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1415938993364681816735123 2123908490047022725102685)
          ·
            refine ⟨796465683767633521913507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2123908490047022725102685 796465683767633521913507)
            ·
              refine ⟨1194698525651450282870261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796465683767633521913507 1194698525651450282870261)
              ·
                refine ⟨112002986779823464019087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1194698525651450282870261 112002986779823464019087)
                ·
                  rfl

theorem cell19_368086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_368086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368086 prefixEnd_368086 := by exact prefixLift 368086
  have htrace : WordTrace (prefixWord ++ tailWord_368086) baseStart_368086 baseEnd_368086 := by
    simpa [prefixWord, tailWord_368086, baseEnd_368086] using wordTrace_append hprefix tailTrace_368086
  have hstable : (prefixWord ++ tailWord_368086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368086).length < 2 ^ (prefixWord ++ tailWord_368086).sum := by decide
  have hdescent : baseEnd_368086 < baseStart_368086 := by decide
  rcases family_descends (prefixWord ++ tailWord_368086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368088 : List Nat := [2, 1, 2, 2, 2, 1, 6, 3]
def baseStart_368088 : Nat := 118140960795 + 368088 * 2 ^ 59
def prefixEnd_368088 : Nat := 4983230072969 + 3 ^ 40 * 368088 * 2
def baseEnd_368088 : Nat := 112003595349488051974637

theorem tailTrace_368088 : CollatzResearch.WordTrace tailWord_368088 prefixEnd_368088 112003595349488051974637 := by
  unfold tailWord_368088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712636145243757635308459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8950181526991676847077945 6712636145243757635308459)
  ·
    refine ⟨10068954217865636452962689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6712636145243757635308459 10068954217865636452962689)
    ·
      refine ⟨7551715663399227339722017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10068954217865636452962689 7551715663399227339722017)
      ·
        refine ⟨5663786747549420504791513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7551715663399227339722017 5663786747549420504791513)
        ·
          refine ⟨4247840060662065378593635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5663786747549420504791513 4247840060662065378593635)
          ·
            refine ⟨6371760090993098067890453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4247840060662065378593635 6371760090993098067890453)
            ·
              refine ⟨298676254265301471932365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6371760090993098067890453 298676254265301471932365)
              ·
                refine ⟨112003595349488051974637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298676254265301471932365 112003595349488051974637)
                ·
                  rfl

theorem cell19_368088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_368088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368088 prefixEnd_368088 := by exact prefixLift 368088
  have htrace : WordTrace (prefixWord ++ tailWord_368088) baseStart_368088 baseEnd_368088 := by
    simpa [prefixWord, tailWord_368088, baseEnd_368088] using wordTrace_append hprefix tailTrace_368088
  have hstable : (prefixWord ++ tailWord_368088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368088).length < 2 ^ (prefixWord ++ tailWord_368088).sum := by decide
  have hdescent : baseEnd_368088 < baseStart_368088 := by decide
  rcases family_descends (prefixWord ++ tailWord_368088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368147 : List Nat := [1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_368147 : Nat := 118140960795 + 368147 * 2 ^ 59
def prefixEnd_368147 : Nat := 4983230072969 + 3 ^ 40 * 368147 * 2
def baseEnd_368147 : Nat := 112021548154593396663365

theorem tailTrace_368147 : CollatzResearch.WordTrace tailWord_368147 prefixEnd_368147 112021548154593396663365 := by
  unfold tailWord_368147
  simp only [CollatzResearch.WordTrace]
  refine ⟨13427424197273768347014695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8951616131515845564676463 13427424197273768347014695)
  ·
    refine ⟨20141136295910652520522043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13427424197273768347014695 20141136295910652520522043)
    ·
      refine ⟨30211704443865978780783065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20141136295910652520522043 30211704443865978780783065)
      ·
        refine ⟨22658778332899484085587299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30211704443865978780783065 22658778332899484085587299)
        ·
          refine ⟨33988167499349226128380949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22658778332899484085587299 33988167499349226128380949)
          ·
            refine ⟨1593195351531994974767857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33988167499349226128380949 1593195351531994974767857)
            ·
              refine ⟨1194896513648996231075893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1593195351531994974767857 1194896513648996231075893)
              ·
                refine ⟨112021548154593396663365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1194896513648996231075893 112021548154593396663365)
                ·
                  rfl

theorem cell19_368147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_368147 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368147 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368147 prefixEnd_368147 := by exact prefixLift 368147
  have htrace : WordTrace (prefixWord ++ tailWord_368147) baseStart_368147 baseEnd_368147 := by
    simpa [prefixWord, tailWord_368147, baseEnd_368147] using wordTrace_append hprefix tailTrace_368147
  have hstable : (prefixWord ++ tailWord_368147).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368147).length < 2 ^ (prefixWord ++ tailWord_368147).sum := by decide
  have hdescent : baseEnd_368147 < baseStart_368147 := by decide
  rcases family_descends (prefixWord ++ tailWord_368147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368158 : List Nat := [4, 3, 3, 1, 2, 6]
def baseStart_368158 : Nat := 118140960795 + 368158 * 2 ^ 59
def prefixEnd_368158 : Nat := 4983230072969 + 3 ^ 40 * 368158 * 2
def baseEnd_368158 : Nat := 12447210587527625602099

theorem tailTrace_368158 : CollatzResearch.WordTrace tailWord_368158 prefixEnd_368158 12447210587527625602099 := by
  unfold tailWord_368158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1678478175029239653208141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8951883600155944817110085 1678478175029239653208141)
  ·
    refine ⟨629429315635964869953053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1678478175029239653208141 629429315635964869953053)
    ·
      refine ⟨236035993363486826232395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 629429315635964869953053 236035993363486826232395)
      ·
        refine ⟨354053990045230239348593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236035993363486826232395 354053990045230239348593)
        ·
          refine ⟨265540492533922679511445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354053990045230239348593 265540492533922679511445)
          ·
            refine ⟨12447210587527625602099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 265540492533922679511445 12447210587527625602099)
            ·
              rfl

theorem cell19_368158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 6].length) (baseStart_368158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368158 prefixEnd_368158 := by exact prefixLift 368158
  have htrace : WordTrace (prefixWord ++ tailWord_368158) baseStart_368158 baseEnd_368158 := by
    simpa [prefixWord, tailWord_368158, baseEnd_368158] using wordTrace_append hprefix tailTrace_368158
  have hstable : (prefixWord ++ tailWord_368158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368158).length < 2 ^ (prefixWord ++ tailWord_368158).sum := by decide
  have hdescent : baseEnd_368158 < baseStart_368158 := by decide
  rcases family_descends (prefixWord ++ tailWord_368158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368183 : List Nat := [1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_368183 : Nat := 118140960795 + 368183 * 2 ^ 59
def prefixEnd_368183 : Nat := 4983230072969 + 3 ^ 40 * 368183 * 2
def baseEnd_368183 : Nat := 112032502408555979863267

theorem tailTrace_368183 : CollatzResearch.WordTrace tailWord_368183 prefixEnd_368183 112032502408555979863267 := by
  unfold tailWord_368183
  simp only [CollatzResearch.WordTrace]
  refine ⟨13428737225143346495325203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8952491483428897663550135 13428737225143346495325203)
  ·
    refine ⟨20143105837715019742987805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13428737225143346495325203 20143105837715019742987805)
    ·
      refine ⟨7553664689143132403620427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20143105837715019742987805 7553664689143132403620427)
      ·
        refine ⟨11330497033714698605430641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7553664689143132403620427 11330497033714698605430641)
        ·
          refine ⟨8497872775286023954072981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11330497033714698605430641 8497872775286023954072981)
          ·
            refine ⟨398337786341532372847171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8497872775286023954072981 398337786341532372847171)
            ·
              refine ⟨597506679512298559270757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398337786341532372847171 597506679512298559270757)
              ·
                refine ⟨112032502408555979863267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 597506679512298559270757 112032502408555979863267)
                ·
                  rfl

theorem cell19_368183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_368183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368183 prefixEnd_368183 := by exact prefixLift 368183
  have htrace : WordTrace (prefixWord ++ tailWord_368183) baseStart_368183 baseEnd_368183 := by
    simpa [prefixWord, tailWord_368183, baseEnd_368183] using wordTrace_append hprefix tailTrace_368183
  have hstable : (prefixWord ++ tailWord_368183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368183).length < 2 ^ (prefixWord ++ tailWord_368183).sum := by decide
  have hdescent : baseEnd_368183 < baseStart_368183 := by decide
  rcases family_descends (prefixWord ++ tailWord_368183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368202 : List Nat := [3, 1, 2, 1, 1, 3, 5, 3]
def baseStart_368202 : Nat := 118140960795 + 368202 * 2 ^ 59
def prefixEnd_368202 : Nat := 4983230072969 + 3 ^ 40 * 368202 * 2
def baseEnd_368202 : Nat := 112038283820369565440993

theorem tailTrace_368202 : CollatzResearch.WordTrace tailWord_368202 prefixEnd_368202 112038283820369565440993 := by
  unfold tailWord_368202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357357553018628185066715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8952953474716341826844573 3357357553018628185066715)
  ·
    refine ⟨5036036329527942277600073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3357357553018628185066715 5036036329527942277600073)
    ·
      refine ⟨3777027247145956708200055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5036036329527942277600073 3777027247145956708200055)
      ·
        refine ⟨5665540870718935062300083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777027247145956708200055 5665540870718935062300083)
        ·
          refine ⟨8498311306078402593450125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665540870718935062300083 8498311306078402593450125)
          ·
            refine ⟨3186866739779400972543797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8498311306078402593450125 3186866739779400972543797)
            ·
              refine ⟨298768756854318841175981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3186866739779400972543797 298768756854318841175981)
              ·
                refine ⟨112038283820369565440993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298768756854318841175981 112038283820369565440993)
                ·
                  rfl

theorem cell19_368202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_368202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368202 prefixEnd_368202 := by exact prefixLift 368202
  have htrace : WordTrace (prefixWord ++ tailWord_368202) baseStart_368202 baseEnd_368202 := by
    simpa [prefixWord, tailWord_368202, baseEnd_368202] using wordTrace_append hprefix tailTrace_368202
  have hstable : (prefixWord ++ tailWord_368202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368202).length < 2 ^ (prefixWord ++ tailWord_368202).sum := by decide
  have hdescent : baseEnd_368202 < baseStart_368202 := by decide
  rcases family_descends (prefixWord ++ tailWord_368202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368257 : List Nat := [1, 2, 4, 2, 1, 4, 2, 3]
def baseStart_368257 : Nat := 118140960795 + 368257 * 2 ^ 59
def prefixEnd_368257 : Nat := 4983230072969 + 3 ^ 40 * 368257 * 2
def baseEnd_368257 : Nat := 112055019486145734218621

theorem tailTrace_368257 : CollatzResearch.WordTrace tailWord_368257 prefixEnd_368257 112055019486145734218621 := by
  unfold tailWord_368257
  simp only [CollatzResearch.WordTrace]
  refine ⟨13431436226875257133519025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8954290817916838089012683 13431436226875257133519025)
  ·
    refine ⟨10073577170156442850139269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13431436226875257133519025 10073577170156442850139269)
    ·
      refine ⟨1888795719404333034401113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10073577170156442850139269 1888795719404333034401113)
      ·
        refine ⟨1416596789553249775800835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1888795719404333034401113 1416596789553249775800835)
        ·
          refine ⟨2124895184329874663701253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416596789553249775800835 2124895184329874663701253)
          ·
            refine ⟨398417847061851499443985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2124895184329874663701253 398417847061851499443985)
            ·
              refine ⟨298813385296388624582989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398417847061851499443985 298813385296388624582989)
              ·
                refine ⟨112055019486145734218621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298813385296388624582989 112055019486145734218621)
                ·
                  rfl

theorem cell19_368257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_368257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368257 prefixEnd_368257 := by exact prefixLift 368257
  have htrace : WordTrace (prefixWord ++ tailWord_368257) baseStart_368257 baseEnd_368257 := by
    simpa [prefixWord, tailWord_368257, baseEnd_368257] using wordTrace_append hprefix tailTrace_368257
  have hstable : (prefixWord ++ tailWord_368257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368257).length < 2 ^ (prefixWord ++ tailWord_368257).sum := by decide
  have hdescent : baseEnd_368257 < baseStart_368257 := by decide
  rcases family_descends (prefixWord ++ tailWord_368257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368261 : List Nat := [1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_368261 : Nat := 118140960795 + 368261 * 2 ^ 59
def prefixEnd_368261 : Nat := 4983230072969 + 3 ^ 40 * 368261 * 2
def baseEnd_368261 : Nat := 112056236625474910129721

theorem tailTrace_368261 : CollatzResearch.WordTrace tailWord_368261 prefixEnd_368261 112056236625474910129721 := by
  unfold tailWord_368261
  simp only [CollatzResearch.WordTrace]
  refine ⟨13431582118860765816664637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8954388079240510544443091 13431582118860765816664637)
  ·
    refine ⟨5036843294572787181249239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13431582118860765816664637 5036843294572787181249239)
    ·
      refine ⟨7555264941859180771873859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5036843294572787181249239 7555264941859180771873859)
      ·
        refine ⟨11332897412788771157810789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7555264941859180771873859 11332897412788771157810789)
        ·
          refine ⟨2124918264897894592089523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11332897412788771157810789 2124918264897894592089523)
          ·
            refine ⟨3187377397346841888134285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124918264897894592089523 3187377397346841888134285)
            ·
              refine ⟨1195266524005065708050357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3187377397346841888134285 1195266524005065708050357)
              ·
                refine ⟨112056236625474910129721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1195266524005065708050357 112056236625474910129721)
                ·
                  rfl

theorem cell19_368261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_368261 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368261 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368261 prefixEnd_368261 := by exact prefixLift 368261
  have htrace : WordTrace (prefixWord ++ tailWord_368261) baseStart_368261 baseEnd_368261 := by
    simpa [prefixWord, tailWord_368261, baseEnd_368261] using wordTrace_append hprefix tailTrace_368261
  have hstable : (prefixWord ++ tailWord_368261).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368261).length < 2 ^ (prefixWord ++ tailWord_368261).sum := by decide
  have hdescent : baseEnd_368261 < baseStart_368261 := by decide
  rcases family_descends (prefixWord ++ tailWord_368261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368276 : List Nat := [2, 4, 2, 2, 2, 2, 5]
def baseStart_368276 : Nat := 118140960795 + 368276 * 2 ^ 59
def prefixEnd_368276 : Nat := 4983230072969 + 3 ^ 40 * 368276 * 2
def baseEnd_368276 : Nat := 37353600299319773265449

theorem tailTrace_368276 : CollatzResearch.WordTrace tailWord_368276 prefixEnd_368276 37353600299319773265449 := by
  unfold tailWord_368276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716064606903211689230341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8954752809204282252307121 6716064606903211689230341)
  ·
    refine ⟨1259262113794352191730689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6716064606903211689230341 1259262113794352191730689)
    ·
      refine ⟨944446585345764143798017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1259262113794352191730689 944446585345764143798017)
      ·
        refine ⟨708334939009323107848513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 944446585345764143798017 708334939009323107848513)
        ·
          refine ⟨531251204256992330886385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708334939009323107848513 531251204256992330886385)
          ·
            refine ⟨398438403192744248164789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531251204256992330886385 398438403192744248164789)
            ·
              refine ⟨37353600299319773265449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398438403192744248164789 37353600299319773265449)
              ·
                rfl

theorem cell19_368276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_368276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368276 prefixEnd_368276 := by exact prefixLift 368276
  have htrace : WordTrace (prefixWord ++ tailWord_368276) baseStart_368276 baseEnd_368276 := by
    simpa [prefixWord, tailWord_368276, baseEnd_368276] using wordTrace_append hprefix tailTrace_368276
  have hstable : (prefixWord ++ tailWord_368276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368276).length < 2 ^ (prefixWord ++ tailWord_368276).sum := by decide
  have hdescent : baseEnd_368276 < baseStart_368276 := by decide
  rcases family_descends (prefixWord ++ tailWord_368276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368280 : List Nat := [2, 1, 2, 4, 1, 2, 7]
def baseStart_368280 : Nat := 118140960795 + 368280 * 2 ^ 59
def prefixEnd_368280 : Nat := 4983230072969 + 3 ^ 40 * 368280 * 2
def baseEnd_368280 : Nat := 37354006012429498569149

theorem tailTrace_368280 : CollatzResearch.WordTrace tailWord_368280 prefixEnd_368280 37354006012429498569149 := by
  unfold tailWord_368280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716137552895966030803147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8954850070527954707737529 6716137552895966030803147)
  ·
    refine ⟨10074206329343949046204721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6716137552895966030803147 10074206329343949046204721)
    ·
      refine ⟨7555654747007961784653541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10074206329343949046204721 7555654747007961784653541)
      ·
        refine ⟨1416685265063992834622539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7555654747007961784653541 1416685265063992834622539)
        ·
          refine ⟨2125027897595989251933809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416685265063992834622539 2125027897595989251933809)
          ·
            refine ⟨1593770923196991938950357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2125027897595989251933809 1593770923196991938950357)
            ·
              refine ⟨37354006012429498569149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1593770923196991938950357 37354006012429498569149)
              ·
                rfl

theorem cell19_368280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_368280 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368280 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368280 prefixEnd_368280 := by exact prefixLift 368280
  have htrace : WordTrace (prefixWord ++ tailWord_368280) baseStart_368280 baseEnd_368280 := by
    simpa [prefixWord, tailWord_368280, baseEnd_368280] using wordTrace_append hprefix tailTrace_368280
  have hstable : (prefixWord ++ tailWord_368280).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368280).length < 2 ^ (prefixWord ++ tailWord_368280).sum := by decide
  have hdescent : baseEnd_368280 < baseStart_368280 := by decide
  rcases family_descends (prefixWord ++ tailWord_368280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368394 : List Nat := [3, 1, 2, 2, 1, 4, 6]
def baseStart_368394 : Nat := 118140960795 + 368394 * 2 ^ 59
def prefixEnd_368394 : Nat := 4983230072969 + 3 ^ 40 * 368394 * 2
def baseEnd_368394 : Nat := 37365568836056669724601

theorem tailTrace_368394 : CollatzResearch.WordTrace tailWord_368394 prefixEnd_368394 37365568836056669724601 := by
  unfold tailWord_368394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359108256844732382814059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8957622018252619687504157 3359108256844732382814059)
  ·
    refine ⟨5038662385267098574221089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3359108256844732382814059 5038662385267098574221089)
    ·
      refine ⟨3778996788950323930665817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5038662385267098574221089 3778996788950323930665817)
      ·
        refine ⟨2834247591712742947999363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3778996788950323930665817 2834247591712742947999363)
        ·
          refine ⟨4251371387569114421999045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834247591712742947999363 4251371387569114421999045)
          ·
            refine ⟨797132135169208954124821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4251371387569114421999045 797132135169208954124821)
            ·
              refine ⟨37365568836056669724601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 797132135169208954124821 37365568836056669724601)
              ·
                rfl

theorem cell19_368394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_368394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368394 prefixEnd_368394 := by exact prefixLift 368394
  have htrace : WordTrace (prefixWord ++ tailWord_368394) baseStart_368394 baseEnd_368394 := by
    simpa [prefixWord, tailWord_368394, baseEnd_368394] using wordTrace_append hprefix tailTrace_368394
  have hstable : (prefixWord ++ tailWord_368394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368394).length < 2 ^ (prefixWord ++ tailWord_368394).sum := by decide
  have hdescent : baseEnd_368394 < baseStart_368394 := by decide
  rcases family_descends (prefixWord ++ tailWord_368394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368451 : List Nat := [1, 1, 1, 3, 1, 7, 5]
def baseStart_368451 : Nat := 118140960795 + 368451 * 2 ^ 59
def prefixEnd_368451 : Nat := 4983230072969 + 3 ^ 40 * 368451 * 2
def baseEnd_368451 : Nat := 37371350247870255302327

theorem tailTrace_368451 : CollatzResearch.WordTrace tailWord_368451 prefixEnd_368451 37371350247870255302327 := by
  unfold tailWord_368451
  simp only [CollatzResearch.WordTrace]
  refine ⟨13438511988172428266081207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8959007992114952177387471 13438511988172428266081207)
  ·
    refine ⟨20157767982258642399121811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13438511988172428266081207 20157767982258642399121811)
    ·
      refine ⟨30236651973387963598682717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20157767982258642399121811 30236651973387963598682717)
      ·
        refine ⟨11338744490020486349506019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30236651973387963598682717 11338744490020486349506019)
        ·
          refine ⟨17008116735030729524259029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11338744490020486349506019 17008116735030729524259029)
          ·
            refine ⟨398627735977282723224821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17008116735030729524259029 398627735977282723224821)
            ·
              refine ⟨37371350247870255302327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398627735977282723224821 37371350247870255302327)
              ·
                rfl

theorem cell19_368451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_368451 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368451 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368451 prefixEnd_368451 := by exact prefixLift 368451
  have htrace : WordTrace (prefixWord ++ tailWord_368451) baseStart_368451 baseEnd_368451 := by
    simpa [prefixWord, tailWord_368451, baseEnd_368451] using wordTrace_append hprefix tailTrace_368451
  have hstable : (prefixWord ++ tailWord_368451).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368451).length < 2 ^ (prefixWord ++ tailWord_368451).sum := by decide
  have hdescent : baseEnd_368451 < baseStart_368451 := by decide
  rcases family_descends (prefixWord ++ tailWord_368451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368468 : List Nat := [2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_368468 : Nat := 118140960795 + 368468 * 2 ^ 59
def prefixEnd_368468 : Nat := 4983230072969 + 3 ^ 40 * 368468 * 2
def baseEnd_368468 : Nat := 112119223585759763529157

theorem tailTrace_368468 : CollatzResearch.WordTrace tailWord_368468 prefixEnd_368468 112119223585759763529157 := by
  unfold tailWord_368468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719566014555420084725029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8959421352740560112966705 6719566014555420084725029)
  ·
    refine ⟨1259918627729141265885943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6719566014555420084725029 1259918627729141265885943)
    ·
      refine ⟨1889877941593711898828915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1259918627729141265885943 1889877941593711898828915)
      ·
        refine ⟨2834816912390567848243373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889877941593711898828915 2834816912390567848243373)
        ·
          refine ⟨1063056342146462943091265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2834816912390567848243373 1063056342146462943091265)
          ·
            refine ⟨797292256609847207318449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1063056342146462943091265 797292256609847207318449)
            ·
              refine ⟨597969192457385405488837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797292256609847207318449 597969192457385405488837)
              ·
                refine ⟨112119223585759763529157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 597969192457385405488837 112119223585759763529157)
                ·
                  rfl

theorem cell19_368468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_368468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368468 prefixEnd_368468 := by exact prefixLift 368468
  have htrace : WordTrace (prefixWord ++ tailWord_368468) baseStart_368468 baseEnd_368468 := by
    simpa [prefixWord, tailWord_368468, baseEnd_368468] using wordTrace_append hprefix tailTrace_368468
  have hstable : (prefixWord ++ tailWord_368468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368468).length < 2 ^ (prefixWord ++ tailWord_368468).sum := by decide
  have hdescent : baseEnd_368468 < baseStart_368468 := by decide
  rcases family_descends (prefixWord ++ tailWord_368468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368565 : List Nat := [1, 3, 3, 2, 1, 3, 6]
def baseStart_368565 : Nat := 118140960795 + 368565 * 2 ^ 59
def prefixEnd_368565 : Nat := 4983230072969 + 3 ^ 40 * 368565 * 2
def baseEnd_368565 : Nat := 37382913071497426457779

theorem tailTrace_368565 : CollatzResearch.WordTrace tailWord_368565 prefixEnd_368565 37382913071497426457779 := by
  unfold tailWord_368565
  simp only [CollatzResearch.WordTrace]
  refine ⟨13442669909759425735731149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8961779939839617157154099 13442669909759425735731149)
  ·
    refine ⟨5041001216159784650899181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13442669909759425735731149 5041001216159784650899181)
    ·
      refine ⟨1890375456059919244087193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5041001216159784650899181 1890375456059919244087193)
      ·
        refine ⟨1417781592044939433065395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1890375456059919244087193 1417781592044939433065395)
        ·
          refine ⟨2126672388067409149598093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417781592044939433065395 2126672388067409149598093)
          ·
            refine ⟨797502145525278431099285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2126672388067409149598093 797502145525278431099285)
            ·
              refine ⟨37382913071497426457779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 797502145525278431099285 37382913071497426457779)
              ·
                rfl

theorem cell19_368565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_368565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368565 prefixEnd_368565 := by exact prefixLift 368565
  have htrace : WordTrace (prefixWord ++ tailWord_368565) baseStart_368565 baseEnd_368565 := by
    simpa [prefixWord, tailWord_368565, baseEnd_368565] using wordTrace_append hprefix tailTrace_368565
  have hstable : (prefixWord ++ tailWord_368565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368565).length < 2 ^ (prefixWord ++ tailWord_368565).sum := by decide
  have hdescent : baseEnd_368565 < baseStart_368565 := by decide
  rcases family_descends (prefixWord ++ tailWord_368565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368622 : List Nat := [4, 1, 2, 1, 3, 1, 7]
def baseStart_368622 : Nat := 118140960795 + 368622 * 2 ^ 59
def prefixEnd_368622 : Nat := 4983230072969 + 3 ^ 40 * 368622 * 2
def baseEnd_368622 : Nat := 37388694483311012035505

theorem tailTrace_368622 : CollatzResearch.WordTrace tailWord_368622 prefixEnd_368622 37388694483311012035505 := by
  unfold tailWord_368622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680593608819115558819515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8963165913701949647037413 1680593608819115558819515)
  ·
    refine ⟨2520890413228673338229273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1680593608819115558819515 2520890413228673338229273)
    ·
      refine ⟨1890667809921505003671955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2520890413228673338229273 1890667809921505003671955)
      ·
        refine ⟨2836001714882257505507933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890667809921505003671955 2836001714882257505507933)
        ·
          refine ⟨1063500643080846564565475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2836001714882257505507933 1063500643080846564565475)
          ·
            refine ⟨1595250964621269846848213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063500643080846564565475 1595250964621269846848213)
            ·
              refine ⟨37388694483311012035505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1595250964621269846848213 37388694483311012035505)
              ·
                rfl

theorem cell19_368622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_368622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368622 prefixEnd_368622 := by exact prefixLift 368622
  have htrace : WordTrace (prefixWord ++ tailWord_368622) baseStart_368622 baseEnd_368622 := by
    simpa [prefixWord, tailWord_368622, baseEnd_368622] using wordTrace_append hprefix tailTrace_368622
  have hstable : (prefixWord ++ tailWord_368622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368622).length < 2 ^ (prefixWord ++ tailWord_368622).sum := by decide
  have hdescent : baseEnd_368622 < baseStart_368622 := by decide
  rcases family_descends (prefixWord ++ tailWord_368622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368624 : List Nat := [2, 1, 1, 1, 3, 2, 9]
def baseStart_368624 : Nat := 118140960795 + 368624 * 2 ^ 59
def prefixEnd_368624 : Nat := 4983230072969 + 3 ^ 40 * 368624 * 2
def baseEnd_368624 : Nat := 37388897339865874687355

theorem tailTrace_368624 : CollatzResearch.WordTrace tailWord_368624 prefixEnd_368624 37388897339865874687355 := by
  unfold tailWord_368624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722410908272839406064463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8963214544363785874752617 6722410908272839406064463)
  ·
    refine ⟨10083616362409259109096695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6722410908272839406064463 10083616362409259109096695)
    ·
      refine ⟨15125424543613888663645043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10083616362409259109096695 15125424543613888663645043)
      ·
        refine ⟨22688136815420832995467565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15125424543613888663645043 22688136815420832995467565)
        ·
          refine ⟨8508051305782812373300337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22688136815420832995467565 8508051305782812373300337)
          ·
            refine ⟨6381038479337109279975253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8508051305782812373300337 6381038479337109279975253)
            ·
              refine ⟨37388897339865874687355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6381038479337109279975253 37388897339865874687355)
              ·
                rfl

theorem cell19_368624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_368624 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368624 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368624 prefixEnd_368624 := by exact prefixLift 368624
  have htrace : WordTrace (prefixWord ++ tailWord_368624) baseStart_368624 baseEnd_368624 := by
    simpa [prefixWord, tailWord_368624, baseEnd_368624] using wordTrace_append hprefix tailTrace_368624
  have hstable : (prefixWord ++ tailWord_368624).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368624).length < 2 ^ (prefixWord ++ tailWord_368624).sum := by decide
  have hdescent : baseEnd_368624 < baseStart_368624 := by decide
  rcases family_descends (prefixWord ++ tailWord_368624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368641 : List Nat := [1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_368641 : Nat := 118140960795 + 368641 * 2 ^ 59
def prefixEnd_368641 : Nat := 4983230072969 + 3 ^ 40 * 368641 * 2
def baseEnd_368641 : Nat := 112171864861746621684241

theorem tailTrace_368641 : CollatzResearch.WordTrace tailWord_368641 prefixEnd_368641 112171864861746621684241 := by
  unfold tailWord_368641
  simp only [CollatzResearch.WordTrace]
  refine ⟨13445441857484090715497777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8963627904989393810331851 13445441857484090715497777)
  ·
    refine ⟨10084081393113068036623333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13445441857484090715497777 10084081393113068036623333)
    ·
      refine ⟨1890765261208700256866875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10084081393113068036623333 1890765261208700256866875)
      ·
        refine ⟨2836147891813050385300313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890765261208700256866875 2836147891813050385300313)
        ·
          refine ⟨2127110918859787788975235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2836147891813050385300313 2127110918859787788975235)
          ·
            refine ⟨3190666378289681683462853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127110918859787788975235 3190666378289681683462853)
            ·
              refine ⟨598249945929315315649285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3190666378289681683462853 598249945929315315649285)
              ·
                refine ⟨112171864861746621684241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598249945929315315649285 112171864861746621684241)
                ·
                  rfl

theorem cell19_368641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_368641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368641 prefixEnd_368641 := by exact prefixLift 368641
  have htrace : WordTrace (prefixWord ++ tailWord_368641) baseStart_368641 baseEnd_368641 := by
    simpa [prefixWord, tailWord_368641, baseEnd_368641] using wordTrace_append hprefix tailTrace_368641
  have hstable : (prefixWord ++ tailWord_368641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368641).length < 2 ^ (prefixWord ++ tailWord_368641).sum := by decide
  have hdescent : baseEnd_368641 < baseStart_368641 := by decide
  rcases family_descends (prefixWord ++ tailWord_368641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368679 : List Nat := [1, 1, 7, 1, 9]
def baseStart_368679 : Nat := 118140960795 + 368679 * 2 ^ 59
def prefixEnd_368679 : Nat := 4983230072969 + 3 ^ 40 * 368679 * 2
def baseEnd_368679 : Nat := 4154941766124955290359

theorem tailTrace_368679 : CollatzResearch.WordTrace tailWord_368679 prefixEnd_368679 4154941766124955290359 := by
  unfold tailWord_368679
  simp only [CollatzResearch.WordTrace]
  refine ⟨13446827831346423205381091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8964551887564282136920727 13446827831346423205381091)
  ·
    refine ⟨20170241747019634808071637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13446827831346423205381091 20170241747019634808071637)
    ·
      refine ⟨472740040945772690814179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 20170241747019634808071637 472740040945772690814179)
      ·
        refine ⟨709110061418659036221269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472740040945772690814179 709110061418659036221269)
        ·
          refine ⟨4154941766124955290359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 709110061418659036221269 4154941766124955290359)
          ·
            rfl

theorem cell19_368679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 9].length) (baseStart_368679 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368679 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368679 prefixEnd_368679 := by exact prefixLift 368679
  have htrace : WordTrace (prefixWord ++ tailWord_368679) baseStart_368679 baseEnd_368679 := by
    simpa [prefixWord, tailWord_368679, baseEnd_368679] using wordTrace_append hprefix tailTrace_368679
  have hstable : (prefixWord ++ tailWord_368679).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368679).length < 2 ^ (prefixWord ++ tailWord_368679).sum := by decide
  have hdescent : baseEnd_368679 < baseStart_368679 := by decide
  rcases family_descends (prefixWord ++ tailWord_368679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368692 : List Nat := [2, 5, 1, 2, 3, 1, 1, 4]
def baseStart_368692 : Nat := 118140960795 + 368692 * 2 ^ 59
def prefixEnd_368692 : Nat := 4983230072969 + 3 ^ 40 * 368692 * 2
def baseEnd_368692 : Nat := 112187383388193614550769

theorem tailTrace_368692 : CollatzResearch.WordTrace tailWord_368692 prefixEnd_368692 112187383388193614550769 := by
  unfold tailWord_368692
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723650990149663212802165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8964867986866217617069553 6723650990149663212802165)
  ·
    refine ⟨630342280326530926200203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6723650990149663212802165 630342280326530926200203)
    ·
      refine ⟨945513420489796389300305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630342280326530926200203 945513420489796389300305)
      ·
        refine ⟨709135065367347291975229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 945513420489796389300305 709135065367347291975229)
        ·
          refine ⟨265925649512755234490711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709135065367347291975229 265925649512755234490711)
          ·
            refine ⟨398888474269132851736067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265925649512755234490711 398888474269132851736067)
            ·
              refine ⟨598332711403699277604101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398888474269132851736067 598332711403699277604101)
              ·
                refine ⟨112187383388193614550769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598332711403699277604101 112187383388193614550769)
                ·
                  rfl

theorem cell19_368692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_368692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368692 prefixEnd_368692 := by exact prefixLift 368692
  have htrace : WordTrace (prefixWord ++ tailWord_368692) baseStart_368692 baseEnd_368692 := by
    simpa [prefixWord, tailWord_368692, baseEnd_368692] using wordTrace_append hprefix tailTrace_368692
  have hstable : (prefixWord ++ tailWord_368692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368692).length < 2 ^ (prefixWord ++ tailWord_368692).sum := by decide
  have hdescent : baseEnd_368692 < baseStart_368692 := by decide
  rcases family_descends (prefixWord ++ tailWord_368692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368696 : List Nat := [2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_368696 : Nat := 118140960795 + 368696 * 2 ^ 59
def prefixEnd_368696 : Nat := 4983230072969 + 3 ^ 40 * 368696 * 2
def baseEnd_368696 : Nat := 112188600527522790461869

theorem tailTrace_368696 : CollatzResearch.WordTrace tailWord_368696 prefixEnd_368696 112188600527522790461869 := by
  unfold tailWord_368696
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723723936142417554374971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8964965248189890072499961 6723723936142417554374971)
  ·
    refine ⟨10085585904213626331562457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6723723936142417554374971 10085585904213626331562457)
    ·
      refine ⟨7564189428160219748671843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10085585904213626331562457 7564189428160219748671843)
      ·
        refine ⟨11346284142240329623007765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7564189428160219748671843 11346284142240329623007765)
        ·
          refine ⟨531857069167515451078489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11346284142240329623007765 531857069167515451078489)
          ·
            refine ⟨398892801875636588308867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531857069167515451078489 398892801875636588308867)
            ·
              refine ⟨598339202813454882463301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398892801875636588308867 598339202813454882463301)
              ·
                refine ⟨112188600527522790461869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598339202813454882463301 112188600527522790461869)
                ·
                  rfl

theorem cell19_368696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_368696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368696 prefixEnd_368696 := by exact prefixLift 368696
  have htrace : WordTrace (prefixWord ++ tailWord_368696) baseStart_368696 baseEnd_368696 := by
    simpa [prefixWord, tailWord_368696, baseEnd_368696] using wordTrace_append hprefix tailTrace_368696
  have hstable : (prefixWord ++ tailWord_368696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368696).length < 2 ^ (prefixWord ++ tailWord_368696).sum := by decide
  have hdescent : baseEnd_368696 < baseStart_368696 := by decide
  rcases family_descends (prefixWord ++ tailWord_368696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368791 : List Nat := [1, 1, 3, 3, 5, 1, 5]
def baseStart_368791 : Nat := 118140960795 + 368791 * 2 ^ 59
def prefixEnd_368791 : Nat := 4983230072969 + 3 ^ 40 * 368791 * 2
def baseEnd_368791 : Nat := 37405835862196906116833

theorem tailTrace_368791 : CollatzResearch.WordTrace tailWord_368791 prefixEnd_368791 37405835862196906116833 := by
  unfold tailWord_368791
  simp only [CollatzResearch.WordTrace]
  refine ⟨13450912806940666333458227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8967275204627110888972151 13450912806940666333458227)
  ·
    refine ⟨20176369210410999500187341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13450912806940666333458227 20176369210410999500187341)
    ·
      refine ⟨7566138453904124812570253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20176369210410999500187341 7566138453904124812570253)
      ·
        refine ⟨2837301920214046804713845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7566138453904124812570253 2837301920214046804713845)
        ·
          refine ⟨265997055020066887941923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2837301920214046804713845 265997055020066887941923)
          ·
            refine ⟨398995582530100331912885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265997055020066887941923 398995582530100331912885)
            ·
              refine ⟨37405835862196906116833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398995582530100331912885 37405835862196906116833)
              ·
                rfl

theorem cell19_368791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 5].length) (baseStart_368791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368791 prefixEnd_368791 := by exact prefixLift 368791
  have htrace : WordTrace (prefixWord ++ tailWord_368791) baseStart_368791 baseEnd_368791 := by
    simpa [prefixWord, tailWord_368791, baseEnd_368791] using wordTrace_append hprefix tailTrace_368791
  have hstable : (prefixWord ++ tailWord_368791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368791).length < 2 ^ (prefixWord ++ tailWord_368791).sum := by decide
  have hdescent : baseEnd_368791 < baseStart_368791 := by decide
  rcases family_descends (prefixWord ++ tailWord_368791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368852 : List Nat := [2, 4, 1, 12]
def baseStart_368852 : Nat := 118140960795 + 368852 * 2 ^ 59
def prefixEnd_368852 : Nat := 4983230072969 + 3 ^ 40 * 368852 * 2
def baseEnd_368852 : Nat := 1385630481004452481417

theorem tailTrace_368852 : CollatzResearch.WordTrace tailWord_368852 prefixEnd_368852 1385630481004452481417 := by
  unfold tailWord_368852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726568829859836875714405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8968758439813115834285873 6726568829859836875714405)
  ·
    refine ⟨1261231655598719414196451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6726568829859836875714405 1261231655598719414196451)
    ·
      refine ⟨1891847483398079121294677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261231655598719414196451 1891847483398079121294677)
      ·
        refine ⟨1385630481004452481417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1891847483398079121294677 1385630481004452481417)
        ·
          rfl

theorem cell19_368852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 12].length) (baseStart_368852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368852 prefixEnd_368852 := by exact prefixLift 368852
  have htrace : WordTrace (prefixWord ++ tailWord_368852) baseStart_368852 baseEnd_368852 := by
    simpa [prefixWord, tailWord_368852, baseEnd_368852] using wordTrace_append hprefix tailTrace_368852
  have hstable : (prefixWord ++ tailWord_368852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368852).length < 2 ^ (prefixWord ++ tailWord_368852).sum := by decide
  have hdescent : baseEnd_368852 < baseStart_368852 := by decide
  rcases family_descends (prefixWord ++ tailWord_368852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368869 : List Nat := [1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_368869 : Nat := 118140960795 + 368869 * 2 ^ 59
def prefixEnd_368869 : Nat := 4983230072969 + 3 ^ 40 * 368869 * 2
def baseEnd_368869 : Nat := 112241241803509648616953

theorem tailTrace_368869 : CollatzResearch.WordTrace tailWord_368869 prefixEnd_368869 112241241803509648616953 := by
  unfold tailWord_368869
  simp only [CollatzResearch.WordTrace]
  refine ⟨13453757700658085654797661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8969171800438723769865107 13453757700658085654797661)
  ·
    refine ⟨5045159137746782120549123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13453757700658085654797661 5045159137746782120549123)
    ·
      refine ⟨7567738706620173180823685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5045159137746782120549123 7567738706620173180823685)
      ·
        refine ⟨1418951007491282471404441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7567738706620173180823685 1418951007491282471404441)
        ·
          refine ⟨1064213255618461853553331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1418951007491282471404441 1064213255618461853553331)
          ·
            refine ⟨1596319883427692780329997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064213255618461853553331 1596319883427692780329997)
            ·
              refine ⟨598619956285384792623749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1596319883427692780329997 598619956285384792623749)
              ·
                refine ⟨112241241803509648616953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598619956285384792623749 112241241803509648616953)
                ·
                  rfl

theorem cell19_368869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_368869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368869 prefixEnd_368869 := by exact prefixLift 368869
  have htrace : WordTrace (prefixWord ++ tailWord_368869) baseStart_368869 baseEnd_368869 := by
    simpa [prefixWord, tailWord_368869, baseEnd_368869] using wordTrace_append hprefix tailTrace_368869
  have hstable : (prefixWord ++ tailWord_368869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368869).length < 2 ^ (prefixWord ++ tailWord_368869).sum := by decide
  have hdescent : baseEnd_368869 < baseStart_368869 := by decide
  rcases family_descends (prefixWord ++ tailWord_368869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368945 : List Nat := [1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_368945 : Nat := 118140960795 + 368945 * 2 ^ 59
def prefixEnd_368945 : Nat := 4983230072969 + 3 ^ 40 * 368945 * 2
def baseEnd_368945 : Nat := 112264367450763990927857

theorem tailTrace_368945 : CollatzResearch.WordTrace tailWord_368945 prefixEnd_368945 112264367450763990927857 := by
  unfold tailWord_368945
  simp only [CollatzResearch.WordTrace]
  refine ⟨13456529648382750634564289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8971019765588500423042859 13456529648382750634564289)
  ·
    refine ⟨10092397236287062975923217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13456529648382750634564289 10092397236287062975923217)
    ·
      refine ⟨7569297927215297231942413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10092397236287062975923217 7569297927215297231942413)
      ·
        refine ⟨2838486722705736461978405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7569297927215297231942413 2838486722705736461978405)
        ·
          refine ⟨532216260507325586620951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2838486722705736461978405 532216260507325586620951)
          ·
            refine ⟨798324390760988379931427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532216260507325586620951 798324390760988379931427)
            ·
              refine ⟨1197486586141482569897141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798324390760988379931427 1197486586141482569897141)
              ·
                refine ⟨112264367450763990927857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1197486586141482569897141 112264367450763990927857)
                ·
                  rfl

theorem cell19_368945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_368945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368945 prefixEnd_368945 := by exact prefixLift 368945
  have htrace : WordTrace (prefixWord ++ tailWord_368945) baseStart_368945 baseEnd_368945 := by
    simpa [prefixWord, tailWord_368945, baseEnd_368945] using wordTrace_append hprefix tailTrace_368945
  have hstable : (prefixWord ++ tailWord_368945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368945).length < 2 ^ (prefixWord ++ tailWord_368945).sum := by decide
  have hdescent : baseEnd_368945 < baseStart_368945 := by decide
  rcases family_descends (prefixWord ++ tailWord_368945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368947 : List Nat := [1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_368947 : Nat := 118140960795 + 368947 * 2 ^ 59
def prefixEnd_368947 : Nat := 4983230072969 + 3 ^ 40 * 368947 * 2
def baseEnd_368947 : Nat := 112264976020428578883407

theorem tailTrace_368947 : CollatzResearch.WordTrace tailWord_368947 prefixEnd_368947 112264976020428578883407 := by
  unfold tailWord_368947
  simp only [CollatzResearch.WordTrace]
  refine ⟨13456602594375504976137095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8971068396250336650758063 13456602594375504976137095)
  ·
    refine ⟨20184903891563257464205643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13456602594375504976137095 20184903891563257464205643)
    ·
      refine ⟨30277355837344886196308465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20184903891563257464205643 30277355837344886196308465)
      ·
        refine ⟨22708016878008664647231349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30277355837344886196308465 22708016878008664647231349)
        ·
          refine ⟨2128876582313312310677939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22708016878008664647231349 2128876582313312310677939)
          ·
            refine ⟨3193314873469968466016909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128876582313312310677939 3193314873469968466016909)
            ·
              refine ⟨1197493077551238174756341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3193314873469968466016909 1197493077551238174756341)
              ·
                refine ⟨112264976020428578883407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1197493077551238174756341 112264976020428578883407)
                ·
                  rfl

theorem cell19_368947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_368947 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_368947 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_368947 prefixEnd_368947 := by exact prefixLift 368947
  have htrace : WordTrace (prefixWord ++ tailWord_368947) baseStart_368947 baseEnd_368947 := by
    simpa [prefixWord, tailWord_368947, baseEnd_368947] using wordTrace_append hprefix tailTrace_368947
  have hstable : (prefixWord ++ tailWord_368947).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368947).length < 2 ^ (prefixWord ++ tailWord_368947).sum := by decide
  have hdescent : baseEnd_368947 < baseStart_368947 := by decide
  rcases family_descends (prefixWord ++ tailWord_368947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369002 : List Nat := [3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_369002 : Nat := 118140960795 + 369002 * 2 ^ 59
def prefixEnd_369002 : Nat := 4983230072969 + 3 ^ 40 * 369002 * 2
def baseEnd_369002 : Nat := 112281711686204747661035

theorem tailTrace_369002 : CollatzResearch.WordTrace tailWord_369002 prefixEnd_369002 112281711686204747661035 := by
  unfold tailWord_369002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3364652152294062342347315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8972405739450832912926173 3364652152294062342347315)
  ·
    refine ⟨5046978228441093513520973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3364652152294062342347315 5046978228441093513520973)
    ·
      refine ⟨1892616835665410067570365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5046978228441093513520973 1892616835665410067570365)
      ·
        refine ⟨709731313374528775338887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1892616835665410067570365 709731313374528775338887)
        ·
          refine ⟨1064596970061793163008331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709731313374528775338887 1064596970061793163008331)
          ·
            refine ⟨1596895455092689744512497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064596970061793163008331 1596895455092689744512497)
            ·
              refine ⟨1197671591319517308384373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596895455092689744512497 1197671591319517308384373)
              ·
                refine ⟨112281711686204747661035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1197671591319517308384373 112281711686204747661035)
                ·
                  rfl

theorem cell19_369002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_369002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369002 prefixEnd_369002 := by exact prefixLift 369002
  have htrace : WordTrace (prefixWord ++ tailWord_369002) baseStart_369002 baseEnd_369002 := by
    simpa [prefixWord, tailWord_369002, baseEnd_369002] using wordTrace_append hprefix tailTrace_369002
  have hstable : (prefixWord ++ tailWord_369002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369002).length < 2 ^ (prefixWord ++ tailWord_369002).sum := by decide
  have hdescent : baseEnd_369002 < baseStart_369002 := by decide
  rcases family_descends (prefixWord ++ tailWord_369002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369038 : List Nat := [4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_369038 : Nat := 118140960795 + 369038 * 2 ^ 59
def prefixEnd_369038 : Nat := 4983230072969 + 3 ^ 40 * 369038 * 2
def baseEnd_369038 : Nat := 112292665940167330860937

theorem tailTrace_369038 : CollatzResearch.WordTrace tailWord_369038 prefixEnd_369038 112292665940167330860937 := by
  unfold tailWord_369038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682490204630728439712471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8973281091363885011799845 1682490204630728439712471)
  ·
    refine ⟨2523735306946092659568707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682490204630728439712471 2523735306946092659568707)
    ·
      refine ⟨3785602960419138989353061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523735306946092659568707 3785602960419138989353061)
      ·
        refine ⟨709800555078588560503699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3785602960419138989353061 709800555078588560503699)
        ·
          refine ⟨1064700832617882840755549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709800555078588560503699 1064700832617882840755549)
          ·
            refine ⟨399262812231706065283331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1064700832617882840755549 399262812231706065283331)
            ·
              refine ⟨598894218347559097924997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399262812231706065283331 598894218347559097924997)
              ·
                refine ⟨112292665940167330860937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598894218347559097924997 112292665940167330860937)
                ·
                  rfl

theorem cell19_369038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_369038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369038 prefixEnd_369038 := by exact prefixLift 369038
  have htrace : WordTrace (prefixWord ++ tailWord_369038) baseStart_369038 baseEnd_369038 := by
    simpa [prefixWord, tailWord_369038, baseEnd_369038] using wordTrace_append hprefix tailTrace_369038
  have hstable : (prefixWord ++ tailWord_369038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369038).length < 2 ^ (prefixWord ++ tailWord_369038).sum := by decide
  have hdescent : baseEnd_369038 < baseStart_369038 := by decide
  rcases family_descends (prefixWord ++ tailWord_369038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369059 : List Nat := [1, 1, 1, 4, 1, 5, 3, 3]
def baseStart_369059 : Nat := 118140960795 + 369059 * 2 ^ 59
def prefixEnd_369059 : Nat := 4983230072969 + 3 ^ 40 * 369059 * 2
def baseEnd_369059 : Nat := 112299055921645504394213

theorem tailTrace_369059 : CollatzResearch.WordTrace tailWord_369059 prefixEnd_369059 112299055921645504394213 := by
  unfold tailWord_369059
  simp only [CollatzResearch.WordTrace]
  refine ⟨13460687569969748104214231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8973791713313165402809487 13460687569969748104214231)
  ·
    refine ⟨20191031354954622156321347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13460687569969748104214231 20191031354954622156321347)
    ·
      refine ⟨30286547032431933234482021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20191031354954622156321347 30286547032431933234482021)
      ·
        refine ⟨5678727568580987481465379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30286547032431933234482021 5678727568580987481465379)
        ·
          refine ⟨8518091352871481222198069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678727568580987481465379 8518091352871481222198069)
          ·
            refine ⟨798571064331701364581069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8518091352871481222198069 798571064331701364581069)
            ·
              refine ⟨299464149124388011717901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 798571064331701364581069 299464149124388011717901)
              ·
                refine ⟨112299055921645504394213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299464149124388011717901 112299055921645504394213)
                ·
                  rfl

theorem cell19_369059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_369059 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369059 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369059 prefixEnd_369059 := by exact prefixLift 369059
  have htrace : WordTrace (prefixWord ++ tailWord_369059) baseStart_369059 baseEnd_369059 := by
    simpa [prefixWord, tailWord_369059, baseEnd_369059] using wordTrace_append hprefix tailTrace_369059
  have hstable : (prefixWord ++ tailWord_369059).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369059).length < 2 ^ (prefixWord ++ tailWord_369059).sum := by decide
  have hdescent : baseEnd_369059 < baseStart_369059 := by decide
  rcases family_descends (prefixWord ++ tailWord_369059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369194 : List Nat := [3, 1, 4, 1, 1, 9]
def baseStart_369194 : Nat := 118140960795 + 369194 * 2 ^ 59
def prefixEnd_369194 : Nat := 4983230072969 + 3 ^ 40 * 369194 * 2
def baseEnd_369194 : Nat := 12482237152667243488205

theorem tailTrace_369194 : CollatzResearch.WordTrace tailWord_369194 prefixEnd_369194 12482237152667243488205 := by
  unfold tailWord_369194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366402856120166540094659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8977074282987110773585757 3366402856120166540094659)
  ·
    refine ⟨5049604284180249810141989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3366402856120166540094659 5049604284180249810141989)
    ·
      refine ⟨946800803283796839401623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5049604284180249810141989 946800803283796839401623)
      ·
        refine ⟨1420201204925695259102435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946800803283796839401623 1420201204925695259102435)
        ·
          refine ⟨2130301807388542888653653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420201204925695259102435 2130301807388542888653653)
          ·
            refine ⟨12482237152667243488205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2130301807388542888653653 12482237152667243488205)
            ·
              rfl

theorem cell19_369194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 9].length) (baseStart_369194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369194 prefixEnd_369194 := by exact prefixLift 369194
  have htrace : WordTrace (prefixWord ++ tailWord_369194) baseStart_369194 baseEnd_369194 := by
    simpa [prefixWord, tailWord_369194, baseEnd_369194] using wordTrace_append hprefix tailTrace_369194
  have hstable : (prefixWord ++ tailWord_369194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369194).length < 2 ^ (prefixWord ++ tailWord_369194).sum := by decide
  have hdescent : baseEnd_369194 < baseStart_369194 := by decide
  rcases family_descends (prefixWord ++ tailWord_369194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369308 : List Nat := [2, 2, 3, 2, 2, 1, 7]
def baseStart_369308 : Nat := 118140960795 + 369308 * 2 ^ 59
def prefixEnd_369308 : Nat := 4983230072969 + 3 ^ 40 * 369308 * 2
def baseEnd_369308 : Nat := 37458274281628901620067

theorem tailTrace_369308 : CollatzResearch.WordTrace tailWord_369308 prefixEnd_369308 37458274281628901620067 := by
  unfold tailWord_369308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6734884673033831815014289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8979846230711775753352385 6734884673033831815014289)
  ·
    refine ⟨5051163504775373861260717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6734884673033831815014289 5051163504775373861260717)
    ·
      refine ⟨1894186314290765197972769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5051163504775373861260717 1894186314290765197972769)
      ·
        refine ⟨1420639735718073898479577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1894186314290765197972769 1420639735718073898479577)
        ·
          refine ⟨1065479801788555423859683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1420639735718073898479577 1065479801788555423859683)
          ·
            refine ⟨1598219702682833135789525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065479801788555423859683 1598219702682833135789525)
            ·
              refine ⟨37458274281628901620067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1598219702682833135789525 37458274281628901620067)
              ·
                rfl

theorem cell19_369308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_369308 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369308 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369308 prefixEnd_369308 := by exact prefixLift 369308
  have htrace : WordTrace (prefixWord ++ tailWord_369308) baseStart_369308 baseEnd_369308 := by
    simpa [prefixWord, tailWord_369308, baseEnd_369308] using wordTrace_append hprefix tailTrace_369308
  have hstable : (prefixWord ++ tailWord_369308).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369308).length < 2 ^ (prefixWord ++ tailWord_369308).sum := by decide
  have hdescent : baseEnd_369308 < baseStart_369308 := by decide
  rcases family_descends (prefixWord ++ tailWord_369308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369325 : List Nat := [1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_369325 : Nat := 118140960795 + 369325 * 2 ^ 59
def prefixEnd_369325 : Nat := 4983230072969 + 3 ^ 40 * 369325 * 2
def baseEnd_369325 : Nat := 112379995687035702482377

theorem tailTrace_369325 : CollatzResearch.WordTrace tailWord_369325 prefixEnd_369325 112379995687035702482377 := by
  unfold tailWord_369325
  simp only [CollatzResearch.WordTrace]
  refine ⟨13470389387006075533397429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8980259591337383688931619 13470389387006075533397429)
  ·
    refine ⟨1262849005031819581256009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13470389387006075533397429 1262849005031819581256009)
    ·
      refine ⟨947136753773864685942007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1262849005031819581256009 947136753773864685942007)
      ·
        refine ⟨1420705130660797028913011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947136753773864685942007 1420705130660797028913011)
        ·
          refine ⟨2131057695991195543369517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420705130660797028913011 2131057695991195543369517)
          ·
            refine ⟨799146635996698328763569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2131057695991195543369517 799146635996698328763569)
            ·
              refine ⟨599359976997523746572677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799146635996698328763569 599359976997523746572677)
              ·
                refine ⟨112379995687035702482377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 599359976997523746572677 112379995687035702482377)
                ·
                  rfl

theorem cell19_369325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_369325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369325 prefixEnd_369325 := by exact prefixLift 369325
  have htrace : WordTrace (prefixWord ++ tailWord_369325) baseStart_369325 baseEnd_369325 := by
    simpa [prefixWord, tailWord_369325, baseEnd_369325] using wordTrace_append hprefix tailTrace_369325
  have hstable : (prefixWord ++ tailWord_369325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369325).length < 2 ^ (prefixWord ++ tailWord_369325).sum := by decide
  have hdescent : baseEnd_369325 < baseStart_369325 := by decide
  rcases family_descends (prefixWord ++ tailWord_369325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369327 : List Nat := [1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_369327 : Nat := 118140960795 + 369327 * 2 ^ 59
def prefixEnd_369327 : Nat := 4983230072969 + 3 ^ 40 * 369327 * 2
def baseEnd_369327 : Nat := 112380604256700290437927

theorem tailTrace_369327 : CollatzResearch.WordTrace tailWord_369327 prefixEnd_369327 112380604256700290437927 := by
  unfold tailWord_369327
  simp only [CollatzResearch.WordTrace]
  refine ⟨13470462332998829874970235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8980308221999219916646823 13470462332998829874970235)
  ·
    refine ⟨20205693499498244812455353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13470462332998829874970235 20205693499498244812455353)
    ·
      refine ⟨15154270124623683609341515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20205693499498244812455353 15154270124623683609341515)
      ·
        refine ⟨22731405186935525414012273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15154270124623683609341515 22731405186935525414012273)
        ·
          refine ⟨17048553890201644060509205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22731405186935525414012273 17048553890201644060509205)
          ·
            refine ⟨799150963603202065336369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17048553890201644060509205 799150963603202065336369)
            ·
              refine ⟨599363222702401549002277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799150963603202065336369 599363222702401549002277)
              ·
                refine ⟨112380604256700290437927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 599363222702401549002277 112380604256700290437927)
                ·
                  rfl

theorem cell19_369327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_369327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369327 prefixEnd_369327 := by exact prefixLift 369327
  have htrace : WordTrace (prefixWord ++ tailWord_369327) baseStart_369327 baseEnd_369327 := by
    simpa [prefixWord, tailWord_369327, baseEnd_369327] using wordTrace_append hprefix tailTrace_369327
  have hstable : (prefixWord ++ tailWord_369327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369327).length < 2 ^ (prefixWord ++ tailWord_369327).sum := by decide
  have hdescent : baseEnd_369327 < baseStart_369327 := by decide
  rcases family_descends (prefixWord ++ tailWord_369327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369365 : List Nat := [1, 3, 2, 5, 8]
def baseStart_369365 : Nat := 118140960795 + 369365 * 2 ^ 59
def prefixEnd_369365 : Nat := 4983230072969 + 3 ^ 40 * 369365 * 2
def baseEnd_369365 : Nat := 4162672854826943021977

theorem tailTrace_369365 : CollatzResearch.WordTrace tailWord_369365 prefixEnd_369365 4162672854826943021977 := by
  unfold tailWord_369365
  simp only [CollatzResearch.WordTrace]
  refine ⟨13471848306861162364853549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8981232204574108243235699 13471848306861162364853549)
  ·
    refine ⟨5051943115072935886820081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13471848306861162364853549 5051943115072935886820081)
    ·
      refine ⟨3788957336304701915115061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5051943115072935886820081 3788957336304701915115061)
      ·
        refine ⟨355214750278565804542037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3788957336304701915115061 355214750278565804542037)
        ·
          refine ⟨4162672854826943021977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 355214750278565804542037 4162672854826943021977)
          ·
            rfl

theorem cell19_369365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 8].length) (baseStart_369365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369365 prefixEnd_369365 := by exact prefixLift 369365
  have htrace : WordTrace (prefixWord ++ tailWord_369365) baseStart_369365 baseEnd_369365 := by
    simpa [prefixWord, tailWord_369365, baseEnd_369365] using wordTrace_append hprefix tailTrace_369365
  have hstable : (prefixWord ++ tailWord_369365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369365).length < 2 ^ (prefixWord ++ tailWord_369365).sum := by decide
  have hdescent : baseEnd_369365 < baseStart_369365 := by decide
  rcases family_descends (prefixWord ++ tailWord_369365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369367 : List Nat := [1, 1, 3, 2, 1, 11]
def baseStart_369367 : Nat := 118140960795 + 369367 * 2 ^ 59
def prefixEnd_369367 : Nat := 4983230072969 + 3 ^ 40 * 369367 * 2
def baseEnd_369367 : Nat := 12488086183332449949881

theorem tailTrace_369367 : CollatzResearch.WordTrace tailWord_369367 prefixEnd_369367 12488086183332449949881 := by
  unfold tailWord_369367
  simp only [CollatzResearch.WordTrace]
  refine ⟨13471921252853916706426355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8981280835235944470950903 13471921252853916706426355)
  ·
    refine ⟨20207881879280875059639533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13471921252853916706426355 20207881879280875059639533)
    ·
      refine ⟨7577955704730328147364825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20207881879280875059639533 7577955704730328147364825)
      ·
        refine ⟨5683466778547746110523619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7577955704730328147364825 5683466778547746110523619)
        ·
          refine ⟨8525200167821619165785429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5683466778547746110523619 8525200167821619165785429)
          ·
            refine ⟨12488086183332449949881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8525200167821619165785429 12488086183332449949881)
            ·
              rfl

theorem cell19_369367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 11].length) (baseStart_369367 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369367 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369367 prefixEnd_369367 := by exact prefixLift 369367
  have htrace : WordTrace (prefixWord ++ tailWord_369367) baseStart_369367 baseEnd_369367 := by
    simpa [prefixWord, tailWord_369367, baseEnd_369367] using wordTrace_append hprefix tailTrace_369367
  have hstable : (prefixWord ++ tailWord_369367).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369367).length < 2 ^ (prefixWord ++ tailWord_369367).sum := by decide
  have hdescent : baseEnd_369367 < baseStart_369367 := by decide
  rcases family_descends (prefixWord ++ tailWord_369367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369443 : List Nat := [1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_369443 : Nat := 118140960795 + 369443 * 2 ^ 59
def prefixEnd_369443 : Nat := 4983230072969 + 3 ^ 40 * 369443 * 2
def baseEnd_369443 : Nat := 112415901297246391859833

theorem tailTrace_369443 : CollatzResearch.WordTrace tailWord_369443 prefixEnd_369443 112415901297246391859833 := by
  unfold tailWord_369443
  simp only [CollatzResearch.WordTrace]
  refine ⟨13474693200578581686192983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8983128800385721124128655 13474693200578581686192983)
  ·
    refine ⟨20212039800867872529289475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13474693200578581686192983 20212039800867872529289475)
    ·
      refine ⟨30318059701301808793934213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20212039800867872529289475 30318059701301808793934213)
      ·
        refine ⟨5684636193994089148862665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30318059701301808793934213 5684636193994089148862665)
        ·
          refine ⟨4263477145495566861646999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5684636193994089148862665 4263477145495566861646999)
          ·
            refine ⟨6395215718243350292470499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263477145495566861646999 6395215718243350292470499)
            ·
              refine ⟨9592823577365025438705749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6395215718243350292470499 9592823577365025438705749)
              ·
                refine ⟨112415901297246391859833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9592823577365025438705749 112415901297246391859833)
                ·
                  rfl

theorem cell19_369443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_369443 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369443 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369443 prefixEnd_369443 := by exact prefixLift 369443
  have htrace : WordTrace (prefixWord ++ tailWord_369443) baseStart_369443 baseEnd_369443 := by
    simpa [prefixWord, tailWord_369443, baseEnd_369443] using wordTrace_append hprefix tailTrace_369443
  have hstable : (prefixWord ++ tailWord_369443).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369443).length < 2 ^ (prefixWord ++ tailWord_369443).sum := by decide
  have hdescent : baseEnd_369443 < baseStart_369443 := by decide
  rcases family_descends (prefixWord ++ tailWord_369443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369481 : List Nat := [1, 2, 1, 1, 2, 5, 7]
def baseStart_369481 : Nat := 118140960795 + 369481 * 2 ^ 59
def prefixEnd_369481 : Nat := 4983230072969 + 3 ^ 40 * 369481 * 2
def baseEnd_369481 : Nat := 37475821373624521005095

theorem tailTrace_369481 : CollatzResearch.WordTrace tailWord_369481 prefixEnd_369481 37475821373624521005095 := by
  unfold tailWord_369481
  simp only [CollatzResearch.WordTrace]
  refine ⟨13476079174440914176076297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8984052782960609450717531 13476079174440914176076297)
  ·
    refine ⟨10107059380830685632057223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13476079174440914176076297 10107059380830685632057223)
    ·
      refine ⟨15160589071246028448085835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10107059380830685632057223 15160589071246028448085835)
      ·
        refine ⟨22740883606869042672128753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15160589071246028448085835 22740883606869042672128753)
        ·
          refine ⟨17055662705151782004096565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22740883606869042672128753 17055662705151782004096565)
          ·
            refine ⟨1598968378607979562884053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17055662705151782004096565 1598968378607979562884053)
            ·
              refine ⟨37475821373624521005095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1598968378607979562884053 37475821373624521005095)
              ·
                rfl

theorem cell19_369481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_369481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369481 prefixEnd_369481 := by exact prefixLift 369481
  have htrace : WordTrace (prefixWord ++ tailWord_369481) baseStart_369481 baseEnd_369481 := by
    simpa [prefixWord, tailWord_369481, baseEnd_369481] using wordTrace_append hprefix tailTrace_369481
  have hstable : (prefixWord ++ tailWord_369481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369481).length < 2 ^ (prefixWord ++ tailWord_369481).sum := by decide
  have hdescent : baseEnd_369481 < baseStart_369481 := by decide
  rcases family_descends (prefixWord ++ tailWord_369481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369498 : List Nat := [3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_369498 : Nat := 118140960795 + 369498 * 2 ^ 59
def prefixEnd_369498 : Nat := 4983230072969 + 3 ^ 40 * 369498 * 2
def baseEnd_369498 : Nat := 112432636963022560637461

theorem tailTrace_369498 : CollatzResearch.WordTrace tailWord_369498 prefixEnd_369498 112432636963022560637461 := by
  unfold tailWord_369498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369174803844831519861287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8984466143586217386296765 3369174803844831519861287)
  ·
    refine ⟨5053762205767247279791931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369174803844831519861287 5053762205767247279791931)
    ·
      refine ⟨7580643308650870919687897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5053762205767247279791931 7580643308650870919687897)
      ·
        refine ⟨5685482481488153189765923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7580643308650870919687897 5685482481488153189765923)
        ·
          refine ⟨8528223722232229784648885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685482481488153189765923 8528223722232229784648885)
          ·
            refine ⟨799520973959271542310833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8528223722232229784648885 799520973959271542310833)
            ·
              refine ⟨599640730469453656733125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799520973959271542310833 599640730469453656733125)
              ·
                refine ⟨112432636963022560637461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 599640730469453656733125 112432636963022560637461)
                ·
                  rfl

theorem cell19_369498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_369498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369498 prefixEnd_369498 := by exact prefixLift 369498
  have htrace : WordTrace (prefixWord ++ tailWord_369498) baseStart_369498 baseEnd_369498 := by
    simpa [prefixWord, tailWord_369498, baseEnd_369498] using wordTrace_append hprefix tailTrace_369498
  have hstable : (prefixWord ++ tailWord_369498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369498).length < 2 ^ (prefixWord ++ tailWord_369498).sum := by decide
  have hdescent : baseEnd_369498 < baseStart_369498 := by decide
  rcases family_descends (prefixWord ++ tailWord_369498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369534 : List Nat := [4, 2, 3, 1, 2, 7]
def baseStart_369534 : Nat := 118140960795 + 369534 * 2 ^ 59
def prefixEnd_369534 : Nat := 4983230072969 + 3 ^ 40 * 369534 * 2
def baseEnd_369534 : Nat := 12493732357442793759707

theorem tailTrace_369534 : CollatzResearch.WordTrace tailWord_369534 prefixEnd_369534 12493732357442793759707 := by
  unfold tailWord_369534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684751530406113028469457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8985341495499269485170437 1684751530406113028469457)
  ·
    refine ⟨1263563647804584771352093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1684751530406113028469457 1263563647804584771352093)
    ·
      refine ⟨473836367926719289257035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1263563647804584771352093 473836367926719289257035)
      ·
        refine ⟨710754551890078933885553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473836367926719289257035 710754551890078933885553)
        ·
          refine ⟨533065913917559200414165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710754551890078933885553 533065913917559200414165)
          ·
            refine ⟨12493732357442793759707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 533065913917559200414165 12493732357442793759707)
            ·
              rfl

theorem cell19_369534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 7].length) (baseStart_369534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369534 prefixEnd_369534 := by exact prefixLift 369534
  have htrace : WordTrace (prefixWord ++ tailWord_369534) baseStart_369534 baseEnd_369534 := by
    simpa [prefixWord, tailWord_369534, baseEnd_369534] using wordTrace_append hprefix tailTrace_369534
  have hstable : (prefixWord ++ tailWord_369534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369534).length < 2 ^ (prefixWord ++ tailWord_369534).sum := by decide
  have hdescent : baseEnd_369534 < baseStart_369534 := by decide
  rcases family_descends (prefixWord ++ tailWord_369534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369629 : List Nat := [1, 4, 3, 1, 2, 1, 4, 3]
def baseStart_369629 : Nat := 118140960795 + 369629 * 2 ^ 59
def prefixEnd_369629 : Nat := 4983230072969 + 3 ^ 40 * 369629 * 2
def baseEnd_369629 : Nat := 112472498276053071725993

theorem tailTrace_369629 : CollatzResearch.WordTrace tailWord_369629 prefixEnd_369629 112472498276053071725993 := by
  unfold tailWord_369629
  simp only [CollatzResearch.WordTrace]
  refine ⟨13481477177904735452463941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8987651451936490301642627 13481477177904735452463941)
  ·
    refine ⟨2527776970857137897336989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13481477177904735452463941 2527776970857137897336989)
    ·
      refine ⟨947916364071426711501371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2527776970857137897336989 947916364071426711501371)
      ·
        refine ⟨1421874546107140067252057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947916364071426711501371 1421874546107140067252057)
        ·
          refine ⟨1066405909580355050439043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1421874546107140067252057 1066405909580355050439043)
          ·
            refine ⟨1599608864370532575658565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066405909580355050439043 1599608864370532575658565)
            ·
              refine ⟨299926662069474857935981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1599608864370532575658565 299926662069474857935981)
              ·
                refine ⟨112472498276053071725993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299926662069474857935981 112472498276053071725993)
                ·
                  rfl

theorem cell19_369629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_369629 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369629 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369629 prefixEnd_369629 := by exact prefixLift 369629
  have htrace : WordTrace (prefixWord ++ tailWord_369629) baseStart_369629 baseEnd_369629 := by
    simpa [prefixWord, tailWord_369629, baseEnd_369629] using wordTrace_append hprefix tailTrace_369629
  have hstable : (prefixWord ++ tailWord_369629).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369629).length < 2 ^ (prefixWord ++ tailWord_369629).sum := by decide
  have hdescent : baseEnd_369629 < baseStart_369629 := by decide
  rcases family_descends (prefixWord ++ tailWord_369629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369631 : List Nat := [1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_369631 : Nat := 118140960795 + 369631 * 2 ^ 59
def prefixEnd_369631 : Nat := 4983230072969 + 3 ^ 40 * 369631 * 2
def baseEnd_369631 : Nat := 112473106845717659681543

theorem tailTrace_369631 : CollatzResearch.WordTrace tailWord_369631 prefixEnd_369631 112473106845717659681543 := by
  unfold tailWord_369631
  simp only [CollatzResearch.WordTrace]
  refine ⟨13481550123897489794036747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8987700082598326529357831 13481550123897489794036747)
  ·
    refine ⟨20222325185846234691055121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13481550123897489794036747 20222325185846234691055121)
    ·
      refine ⟨15166743889384676018291341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20222325185846234691055121 15166743889384676018291341)
      ·
        refine ⟨5687528958519253506859253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15166743889384676018291341 5687528958519253506859253)
        ·
          refine ⟨533205839861180016268055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5687528958519253506859253 533205839861180016268055)
          ·
            refine ⟨799808759791770024402083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533205839861180016268055 799808759791770024402083)
            ·
              refine ⟨1199713139687655036603125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799808759791770024402083 1199713139687655036603125)
              ·
                refine ⟨112473106845717659681543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1199713139687655036603125 112473106845717659681543)
                ·
                  rfl

theorem cell19_369631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_369631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369631 prefixEnd_369631 := by exact prefixLift 369631
  have htrace : WordTrace (prefixWord ++ tailWord_369631) baseStart_369631 baseEnd_369631 := by
    simpa [prefixWord, tailWord_369631, baseEnd_369631] using wordTrace_append hprefix tailTrace_369631
  have hstable : (prefixWord ++ tailWord_369631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369631).length < 2 ^ (prefixWord ++ tailWord_369631).sum := by decide
  have hdescent : baseEnd_369631 < baseStart_369631 := by decide
  rcases family_descends (prefixWord ++ tailWord_369631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369690 : List Nat := [3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_369690 : Nat := 118140960795 + 369690 * 2 ^ 59
def prefixEnd_369690 : Nat := 4983230072969 + 3 ^ 40 * 369690 * 2
def baseEnd_369690 : Nat := 112491059650823004370271

theorem tailTrace_369690 : CollatzResearch.WordTrace tailWord_369690 prefixEnd_369690 112491059650823004370271 := by
  unfold tailWord_369690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3370925507670935717608631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8989134687122495246956349 3370925507670935717608631)
  ·
    refine ⟨5056388261506403576412947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3370925507670935717608631 5056388261506403576412947)
    ·
      refine ⟨7584582392259605364619421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5056388261506403576412947 7584582392259605364619421)
      ·
        refine ⟨2844218397097352011732283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7584582392259605364619421 2844218397097352011732283)
        ·
          refine ⟨4266327595646028017598425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844218397097352011732283 4266327595646028017598425)
          ·
            refine ⟨3199745696734521013198819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4266327595646028017598425 3199745696734521013198819)
            ·
              refine ⟨4799618545101781519798229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199745696734521013198819 4799618545101781519798229)
              ·
                refine ⟨112491059650823004370271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4799618545101781519798229 112491059650823004370271)
                ·
                  rfl

theorem cell19_369690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_369690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369690 prefixEnd_369690 := by exact prefixLift 369690
  have htrace : WordTrace (prefixWord ++ tailWord_369690) baseStart_369690 baseEnd_369690 := by
    simpa [prefixWord, tailWord_369690, baseEnd_369690] using wordTrace_append hprefix tailTrace_369690
  have hstable : (prefixWord ++ tailWord_369690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369690).length < 2 ^ (prefixWord ++ tailWord_369690).sum := by decide
  have hdescent : baseEnd_369690 < baseStart_369690 := by decide
  rcases family_descends (prefixWord ++ tailWord_369690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369842 : List Nat := [3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_369842 : Nat := 118140960795 + 369842 * 2 ^ 59
def prefixEnd_369842 : Nat := 4983230072969 + 3 ^ 40 * 369842 * 2
def baseEnd_369842 : Nat := 112537310945331688992079

theorem tailTrace_369842 : CollatzResearch.WordTrace tailWord_369842 prefixEnd_369842 112537310945331688992079 := by
  unfold tailWord_369842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372311481533268207491945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8992830617422048553311853 3372311481533268207491945)
  ·
    refine ⟨2529233611149951155618959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3372311481533268207491945 2529233611149951155618959)
    ·
      refine ⟨3793850416724926733428439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2529233611149951155618959 3793850416724926733428439)
      ·
        refine ⟨5690775625087390100142659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793850416724926733428439 5690775625087390100142659)
        ·
          refine ⟨8536163437631085150213989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690775625087390100142659 8536163437631085150213989)
          ·
            refine ⟨1600530644555828465665123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8536163437631085150213989 1600530644555828465665123)
            ·
              refine ⟨2400795966833742698497685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600530644555828465665123 2400795966833742698497685)
              ·
                refine ⟨112537310945331688992079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2400795966833742698497685 112537310945331688992079)
                ·
                  rfl

theorem cell19_369842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_369842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369842 prefixEnd_369842 := by exact prefixLift 369842
  have htrace : WordTrace (prefixWord ++ tailWord_369842) baseStart_369842 baseEnd_369842 := by
    simpa [prefixWord, tailWord_369842, baseEnd_369842] using wordTrace_append hprefix tailTrace_369842
  have hstable : (prefixWord ++ tailWord_369842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369842).length < 2 ^ (prefixWord ++ tailWord_369842).sum := by decide
  have hdescent : baseEnd_369842 < baseStart_369842 := by decide
  rcases family_descends (prefixWord ++ tailWord_369842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369876 : List Nat := [2, 4, 1, 4, 2, 6]
def baseStart_369876 : Nat := 118140960795 + 369876 * 2 ^ 59
def prefixEnd_369876 : Nat := 4983230072969 + 3 ^ 40 * 369876 * 2
def baseEnd_369876 : Nat := 12505295181069964915159

theorem tailTrace_369876 : CollatzResearch.WordTrace tailWord_369876 prefixEnd_369876 12505295181069964915159 := by
  unfold tailWord_369876
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745243004004948318352741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8993657338673264424470321 6745243004004948318352741)
  ·
    refine ⟨1264733063250927809691139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6745243004004948318352741 1264733063250927809691139)
    ·
      refine ⟨1897099594876391714536709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264733063250927809691139 1897099594876391714536709)
      ·
        refine ⟨355706174039323446475633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1897099594876391714536709 355706174039323446475633)
        ·
          refine ⟨266779630529492584856725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355706174039323446475633 266779630529492584856725)
          ·
            refine ⟨12505295181069964915159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 266779630529492584856725 12505295181069964915159)
            ·
              rfl

theorem cell19_369876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 6].length) (baseStart_369876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369876 prefixEnd_369876 := by exact prefixLift 369876
  have htrace : WordTrace (prefixWord ++ tailWord_369876) baseStart_369876 baseEnd_369876 := by
    simpa [prefixWord, tailWord_369876, baseEnd_369876] using wordTrace_append hprefix tailTrace_369876
  have hstable : (prefixWord ++ tailWord_369876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369876).length < 2 ^ (prefixWord ++ tailWord_369876).sum := by decide
  have hdescent : baseEnd_369876 < baseStart_369876 := by decide
  rcases family_descends (prefixWord ++ tailWord_369876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369878 : List Nat := [5, 2, 1, 2, 9]
def baseStart_369878 : Nat := 118140960795 + 369878 * 2 ^ 59
def prefixEnd_369878 : Nat := 4983230072969 + 3 ^ 40 * 369878 * 2
def baseEnd_369878 : Nat := 4168454266640528599703

theorem tailTrace_369878 : CollatzResearch.WordTrace tailWord_369878 prefixEnd_369878 4168454266640528599703 := by
  unfold tailWord_369878
  simp only [CollatzResearch.WordTrace]
  refine ⟨843159934625165686142393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8993705969335100652185525 843159934625165686142393)
  ·
    refine ⟨632369950968874264606795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 843159934625165686142393 632369950968874264606795)
    ·
      refine ⟨948554926453311396910193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 632369950968874264606795 948554926453311396910193)
      ·
        refine ⟨711416194839983547682645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 948554926453311396910193 711416194839983547682645)
        ·
          refine ⟨4168454266640528599703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 711416194839983547682645 4168454266640528599703)
          ·
            rfl

theorem cell19_369878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 9].length) (baseStart_369878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369878 prefixEnd_369878 := by exact prefixLift 369878
  have htrace : WordTrace (prefixWord ++ tailWord_369878) baseStart_369878 baseEnd_369878 := by
    simpa [prefixWord, tailWord_369878, baseEnd_369878] using wordTrace_append hprefix tailTrace_369878
  have hstable : (prefixWord ++ tailWord_369878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369878).length < 2 ^ (prefixWord ++ tailWord_369878).sum := by decide
  have hdescent : baseEnd_369878 < baseStart_369878 := by decide
  rcases family_descends (prefixWord ++ tailWord_369878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369880 : List Nat := [2, 1, 2, 2, 5, 7]
def baseStart_369880 : Nat := 118140960795 + 369880 * 2 ^ 59
def prefixEnd_369880 : Nat := 4983230072969 + 3 ^ 40 * 369880 * 2
def baseEnd_369880 : Nat := 12505430418773206683059

theorem tailTrace_369880 : CollatzResearch.WordTrace tailWord_369880 prefixEnd_369880 12505430418773206683059 := by
  unfold tailWord_369880
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745315949997702659925547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8993754599996936879900729 6745315949997702659925547)
  ·
    refine ⟨10117973924996553989888321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6745315949997702659925547 10117973924996553989888321)
    ·
      refine ⟨7588480443747415492416241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10117973924996553989888321 7588480443747415492416241)
      ·
        refine ⟨5691360332810561619312181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7588480443747415492416241 5691360332810561619312181)
        ·
          refine ⟨533565031200990151810517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5691360332810561619312181 533565031200990151810517)
          ·
            refine ⟨12505430418773206683059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 533565031200990151810517 12505430418773206683059)
            ·
              rfl

theorem cell19_369880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 7].length) (baseStart_369880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369880 prefixEnd_369880 := by exact prefixLift 369880
  have htrace : WordTrace (prefixWord ++ tailWord_369880) baseStart_369880 baseEnd_369880 := by
    simpa [prefixWord, tailWord_369880, baseEnd_369880] using wordTrace_append hprefix tailTrace_369880
  have hstable : (prefixWord ++ tailWord_369880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369880).length < 2 ^ (prefixWord ++ tailWord_369880).sum := by decide
  have hdescent : baseEnd_369880 < baseStart_369880 := by decide
  rcases family_descends (prefixWord ++ tailWord_369880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369895 : List Nat := [1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_369895 : Nat := 118140960795 + 369895 * 2 ^ 59
def prefixEnd_369895 : Nat := 4983230072969 + 3 ^ 40 * 369895 * 2
def baseEnd_369895 : Nat := 112553438041443269814157

theorem tailTrace_369895 : CollatzResearch.WordTrace tailWord_369895 prefixEnd_369895 112553438041443269814157 := by
  unfold tailWord_369895
  simp only [CollatzResearch.WordTrace]
  refine ⟨13491178994941062881647139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8994119329960708587764759 13491178994941062881647139)
  ·
    refine ⟨20236768492411594322470709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13491178994941062881647139 20236768492411594322470709)
    ·
      refine ⟨1897197046163586967731629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20236768492411594322470709 1897197046163586967731629)
      ·
        refine ⟨711448892311345112899361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1897197046163586967731629 711448892311345112899361)
        ·
          refine ⟨533586669233508834674521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 711448892311345112899361 533586669233508834674521)
          ·
            refine ⟨400190001925131626005891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533586669233508834674521 400190001925131626005891)
            ·
              refine ⟨600285002887697439008837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400190001925131626005891 600285002887697439008837)
              ·
                refine ⟨112553438041443269814157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600285002887697439008837 112553438041443269814157)
                ·
                  rfl

theorem cell19_369895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_369895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369895 prefixEnd_369895 := by exact prefixLift 369895
  have htrace : WordTrace (prefixWord ++ tailWord_369895) baseStart_369895 baseEnd_369895 := by
    simpa [prefixWord, tailWord_369895, baseEnd_369895] using wordTrace_append hprefix tailTrace_369895
  have hstable : (prefixWord ++ tailWord_369895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369895).length < 2 ^ (prefixWord ++ tailWord_369895).sum := by decide
  have hdescent : baseEnd_369895 < baseStart_369895 := by decide
  rcases family_descends (prefixWord ++ tailWord_369895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369899 : List Nat := [1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_369899 : Nat := 118140960795 + 369899 * 2 ^ 59
def prefixEnd_369899 : Nat := 4983230072969 + 3 ^ 40 * 369899 * 2
def baseEnd_369899 : Nat := 112554655180772445725257

theorem tailTrace_369899 : CollatzResearch.WordTrace tailWord_369899 prefixEnd_369899 112554655180772445725257 := by
  unfold tailWord_369899
  simp only [CollatzResearch.WordTrace]
  refine ⟨13491324886926571564792751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8994216591284381043195167 13491324886926571564792751)
  ·
    refine ⟨20236987330389857347189127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13491324886926571564792751 20236987330389857347189127)
    ·
      refine ⟨30355480995584786020783691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20236987330389857347189127 30355480995584786020783691)
      ·
        refine ⟨45533221493377179031175537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30355480995584786020783691 45533221493377179031175537)
        ·
          refine ⟨34149916120032884273381653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45533221493377179031175537 34149916120032884273381653)
          ·
            refine ⟨1600777318126541450314765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34149916120032884273381653 1600777318126541450314765)
            ·
              refine ⟨600291494297453043868037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1600777318126541450314765 600291494297453043868037)
              ·
                refine ⟨112554655180772445725257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600291494297453043868037 112554655180772445725257)
                ·
                  rfl

theorem cell19_369899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_369899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369899 prefixEnd_369899 := by exact prefixLift 369899
  have htrace : WordTrace (prefixWord ++ tailWord_369899) baseStart_369899 baseEnd_369899 := by
    simpa [prefixWord, tailWord_369899, baseEnd_369899] using wordTrace_append hprefix tailTrace_369899
  have hstable : (prefixWord ++ tailWord_369899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369899).length < 2 ^ (prefixWord ++ tailWord_369899).sum := by decide
  have hdescent : baseEnd_369899 < baseStart_369899 := by decide
  rcases family_descends (prefixWord ++ tailWord_369899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369956 : List Nat := [2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_369956 : Nat := 118140960795 + 369956 * 2 ^ 59
def prefixEnd_369956 : Nat := 4983230072969 + 3 ^ 40 * 369956 * 2
def baseEnd_369956 : Nat := 112571999416213202458435

theorem tailTrace_369956 : CollatzResearch.WordTrace tailWord_369956 prefixEnd_369956 112571999416213202458435 := by
  unfold tailWord_369956
  simp only [CollatzResearch.WordTrace]
  refine ⟨6746701923860035149808861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8995602565146713533078481 6746701923860035149808861)
  ·
    refine ⟨2530013221447513181178323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6746701923860035149808861 2530013221447513181178323)
    ·
      refine ⟨3795019832171269771767485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2530013221447513181178323 3795019832171269771767485)
      ·
        refine ⟨1423132437064226164412807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3795019832171269771767485 1423132437064226164412807)
        ·
          refine ⟨2134698655596339246619211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423132437064226164412807 2134698655596339246619211)
          ·
            refine ⟨3202047983394508869928817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134698655596339246619211 3202047983394508869928817)
            ·
              refine ⟨2401535987545881652446613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3202047983394508869928817 2401535987545881652446613)
              ·
                refine ⟨112571999416213202458435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2401535987545881652446613 112571999416213202458435)
                ·
                  rfl

theorem cell19_369956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_369956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369956 prefixEnd_369956 := by exact prefixLift 369956
  have htrace : WordTrace (prefixWord ++ tailWord_369956) baseStart_369956 baseEnd_369956 := by
    simpa [prefixWord, tailWord_369956, baseEnd_369956] using wordTrace_append hprefix tailTrace_369956
  have hstable : (prefixWord ++ tailWord_369956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369956).length < 2 ^ (prefixWord ++ tailWord_369956).sum := by decide
  have hdescent : baseEnd_369956 < baseStart_369956 := by decide
  rcases family_descends (prefixWord ++ tailWord_369956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369973 : List Nat := [1, 3, 3, 1, 2, 2, 4, 3]
def baseStart_369973 : Nat := 118140960795 + 369973 * 2 ^ 59
def prefixEnd_369973 : Nat := 4983230072969 + 3 ^ 40 * 369973 * 2
def baseEnd_369973 : Nat := 112577172258362200080611

theorem tailTrace_369973 : CollatzResearch.WordTrace tailWord_369973 prefixEnd_369973 112577172258362200080611 := by
  unfold tailWord_369973
  simp only [CollatzResearch.WordTrace]
  refine ⟨13494023888658482202986573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8996015925772321468657715 13494023888658482202986573)
  ·
    refine ⟨5060258958246930826119965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13494023888658482202986573 5060258958246930826119965)
    ·
      refine ⟨1897597109342599059794987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5060258958246930826119965 1897597109342599059794987)
      ·
        refine ⟨2846395664013898589692481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897597109342599059794987 2846395664013898589692481)
        ·
          refine ⟨2134796748010423942269361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2846395664013898589692481 2134796748010423942269361)
          ·
            refine ⟨1601097561007817956702021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134796748010423942269361 1601097561007817956702021)
            ·
              refine ⟨300205792688965866881629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1601097561007817956702021 300205792688965866881629)
              ·
                refine ⟨112577172258362200080611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300205792688965866881629 112577172258362200080611)
                ·
                  rfl

theorem cell19_369973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_369973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_369973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_369973 prefixEnd_369973 := by exact prefixLift 369973
  have htrace : WordTrace (prefixWord ++ tailWord_369973) baseStart_369973 baseEnd_369973 := by
    simpa [prefixWord, tailWord_369973, baseEnd_369973] using wordTrace_append hprefix tailTrace_369973
  have hstable : (prefixWord ++ tailWord_369973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369973).length < 2 ^ (prefixWord ++ tailWord_369973).sum := by decide
  have hdescent : baseEnd_369973 < baseStart_369973 := by decide
  rcases family_descends (prefixWord ++ tailWord_369973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370049 : List Nat := [1, 2, 4, 3, 3, 6]
def baseStart_370049 : Nat := 118140960795 + 370049 * 2 ^ 59
def prefixEnd_370049 : Nat := 4983230072969 + 3 ^ 40 * 370049 * 2
def baseEnd_370049 : Nat := 12511144211735171376835

theorem tailTrace_370049 : CollatzResearch.WordTrace tailWord_370049 prefixEnd_370049 12511144211735171376835 := by
  unfold tailWord_370049
  simp only [CollatzResearch.WordTrace]
  refine ⟨13496795836383147182753201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8997863890922098121835467 13496795836383147182753201)
  ·
    refine ⟨10122596877287360387064901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13496795836383147182753201 10122596877287360387064901)
    ·
      refine ⟨1897986914491380072574669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10122596877287360387064901 1897986914491380072574669)
      ·
        refine ⟨711745092934267527215501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1897986914491380072574669 711745092934267527215501)
        ·
          refine ⟨266904409850350322705813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 711745092934267527215501 266904409850350322705813)
          ·
            refine ⟨12511144211735171376835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 266904409850350322705813 12511144211735171376835)
            ·
              rfl

theorem cell19_370049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 6].length) (baseStart_370049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370049 prefixEnd_370049 := by exact prefixLift 370049
  have htrace : WordTrace (prefixWord ++ tailWord_370049) baseStart_370049 baseEnd_370049 := by
    simpa [prefixWord, tailWord_370049, baseEnd_370049] using wordTrace_append hprefix tailTrace_370049
  have hstable : (prefixWord ++ tailWord_370049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370049).length < 2 ^ (prefixWord ++ tailWord_370049).sum := by decide
  have hdescent : baseEnd_370049 < baseStart_370049 := by decide
  rcases family_descends (prefixWord ++ tailWord_370049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370068 : List Nat := [2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_370068 : Nat := 118140960795 + 370068 * 2 ^ 59
def prefixEnd_370068 : Nat := 4983230072969 + 3 ^ 40 * 370068 * 2
def baseEnd_370068 : Nat := 112606079317430127969241

theorem tailTrace_370068 : CollatzResearch.WordTrace tailWord_370068 prefixEnd_370068 112606079317430127969241 := by
  unfold tailWord_370068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748744411657156713847429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8998325882209542285129905 6748744411657156713847429)
  ·
    refine ⟨1265389577185716883846393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6748744411657156713847429 1265389577185716883846393)
    ·
      refine ⟨949042182889287662884795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1265389577185716883846393 949042182889287662884795)
      ·
        refine ⟨1423563274333931494327193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949042182889287662884795 1423563274333931494327193)
        ·
          refine ⟨1067672455750448620745395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1423563274333931494327193 1067672455750448620745395)
          ·
            refine ⟨1601508683625672931118093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067672455750448620745395 1601508683625672931118093)
            ·
              refine ⟨600565756359627349169285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1601508683625672931118093 600565756359627349169285)
              ·
                refine ⟨112606079317430127969241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600565756359627349169285 112606079317430127969241)
                ·
                  rfl

theorem cell19_370068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_370068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370068 prefixEnd_370068 := by exact prefixLift 370068
  have htrace : WordTrace (prefixWord ++ tailWord_370068) baseStart_370068 baseEnd_370068 := by
    simpa [prefixWord, tailWord_370068, baseEnd_370068] using wordTrace_append hprefix tailTrace_370068
  have hstable : (prefixWord ++ tailWord_370068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370068).length < 2 ^ (prefixWord ++ tailWord_370068).sum := by decide
  have hdescent : baseEnd_370068 < baseStart_370068 := by decide
  rcases family_descends (prefixWord ++ tailWord_370068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370087 : List Nat := [1, 1, 6, 1, 1, 1, 5, 3]
def baseStart_370087 : Nat := 118140960795 + 370087 * 2 ^ 59
def prefixEnd_370087 : Nat := 4983230072969 + 3 ^ 40 * 370087 * 2
def baseEnd_370087 : Nat := 112611860729243713546967

theorem tailTrace_370087 : CollatzResearch.WordTrace tailWord_370087 prefixEnd_370087 112611860729243713546967 := by
  unfold tailWord_370087
  simp only [CollatzResearch.WordTrace]
  refine ⟨13498181810245479672636515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8998787873496986448424343 13498181810245479672636515)
  ·
    refine ⟨20247272715368219508954773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13498181810245479672636515 20247272715368219508954773)
    ·
      refine ⟨949090908532885289482255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20247272715368219508954773 949090908532885289482255)
      ·
        refine ⟨1423636362799327934223383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949090908532885289482255 1423636362799327934223383)
        ·
          refine ⟨2135454544198991901335075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423636362799327934223383 2135454544198991901335075)
          ·
            refine ⟨3203181816298487852002613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135454544198991901335075 3203181816298487852002613)
            ·
              refine ⟨300298295277983236125245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3203181816298487852002613 300298295277983236125245)
              ·
                refine ⟨112611860729243713546967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300298295277983236125245 112611860729243713546967)
                ·
                  rfl

theorem cell19_370087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_370087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370087 prefixEnd_370087 := by exact prefixLift 370087
  have htrace : WordTrace (prefixWord ++ tailWord_370087) baseStart_370087 baseEnd_370087 := by
    simpa [prefixWord, tailWord_370087, baseEnd_370087] using wordTrace_append hprefix tailTrace_370087
  have hstable : (prefixWord ++ tailWord_370087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370087).length < 2 ^ (prefixWord ++ tailWord_370087).sum := by decide
  have hdescent : baseEnd_370087 < baseStart_370087 := by decide
  rcases family_descends (prefixWord ++ tailWord_370087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370222 : List Nat := [4, 1, 3, 1, 2, 8]
def baseStart_370222 : Nat := 118140960795 + 370222 * 2 ^ 59
def prefixEnd_370222 : Nat := 4983230072969 + 3 ^ 40 * 370222 * 2
def baseEnd_370222 : Nat := 12516993242400377838511

theorem tailTrace_370222 : CollatzResearch.WordTrace tailWord_370222 prefixEnd_370222 12516993242400377838511 := by
  unfold tailWord_370222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687888208094549716100115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9002070443170931819200613 1687888208094549716100115)
  ·
    refine ⟨2531832312141824574150173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1687888208094549716100115 2531832312141824574150173)
    ·
      refine ⟨949437117053184215306315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2531832312141824574150173 949437117053184215306315)
      ·
        refine ⟨1424155675579776322959473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949437117053184215306315 1424155675579776322959473)
        ·
          refine ⟨1068116756684832242219605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424155675579776322959473 1068116756684832242219605)
          ·
            refine ⟨12516993242400377838511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1068116756684832242219605 12516993242400377838511)
            ·
              rfl

theorem cell19_370222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 8].length) (baseStart_370222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370222 prefixEnd_370222 := by exact prefixLift 370222
  have htrace : WordTrace (prefixWord ++ tailWord_370222) baseStart_370222 baseEnd_370222 := by
    simpa [prefixWord, tailWord_370222, baseEnd_370222] using wordTrace_append hprefix tailTrace_370222
  have hstable : (prefixWord ++ tailWord_370222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370222).length < 2 ^ (prefixWord ++ tailWord_370222).sum := by decide
  have hdescent : baseEnd_370222 < baseStart_370222 := by decide
  rcases family_descends (prefixWord ++ tailWord_370222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370237 : List Nat := [1, 4, 1, 3, 4, 1, 1, 4]
def baseStart_370237 : Nat := 118140960795 + 370237 * 2 ^ 59
def prefixEnd_370237 : Nat := 4983230072969 + 3 ^ 40 * 370237 * 2
def baseEnd_370237 : Nat := 112657503454087810213225

theorem tailTrace_370237 : CollatzResearch.WordTrace tailWord_370237 prefixEnd_370237 112657503454087810213225 := by
  unfold tailWord_370237
  simp only [CollatzResearch.WordTrace]
  refine ⟨13503652759702055290596965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9002435173134703527064643 13503652759702055290596965)
  ·
    refine ⟨2531934892444135366986931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13503652759702055290596965 2531934892444135366986931)
    ·
      refine ⟨3797902338666203050480397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531934892444135366986931 3797902338666203050480397)
      ·
        refine ⟨1424213376999826143930149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3797902338666203050480397 1424213376999826143930149)
        ·
          refine ⟨267040008187467401986903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1424213376999826143930149 267040008187467401986903)
          ·
            refine ⟨400560012281201102980355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267040008187467401986903 400560012281201102980355)
            ·
              refine ⟨600840018421801654470533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400560012281201102980355 600840018421801654470533)
              ·
                refine ⟨112657503454087810213225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600840018421801654470533 112657503454087810213225)
                ·
                  rfl

theorem cell19_370237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 4].length) (baseStart_370237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370237 prefixEnd_370237 := by exact prefixLift 370237
  have htrace : WordTrace (prefixWord ++ tailWord_370237) baseStart_370237 baseEnd_370237 := by
    simpa [prefixWord, tailWord_370237, baseEnd_370237] using wordTrace_append hprefix tailTrace_370237
  have hstable : (prefixWord ++ tailWord_370237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370237).length < 2 ^ (prefixWord ++ tailWord_370237).sum := by decide
  have hdescent : baseEnd_370237 < baseStart_370237 := by decide
  rcases family_descends (prefixWord ++ tailWord_370237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370258 : List Nat := [3, 2, 2, 1, 2, 3, 3, 3]
def baseStart_370258 : Nat := 118140960795 + 370258 * 2 ^ 59
def prefixEnd_370258 : Nat := 4983230072969 + 3 ^ 40 * 370258 * 2
def baseEnd_370258 : Nat := 112663893435565983746501

theorem tailTrace_370258 : CollatzResearch.WordTrace tailWord_370258 prefixEnd_370258 112663893435565983746501 := by
  unfold tailWord_370258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376104673156493969277857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9002945795083983918074285 3376104673156493969277857)
  ·
    refine ⟨2532078504867370476958393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3376104673156493969277857 2532078504867370476958393)
    ·
      refine ⟨1899058878650527857718795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2532078504867370476958393 1899058878650527857718795)
      ·
        refine ⟨2848588317975791786578193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899058878650527857718795 2848588317975791786578193)
        ·
          refine ⟨2136441238481843839933645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848588317975791786578193 2136441238481843839933645)
          ·
            refine ⟨801165464430691439975117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2136441238481843839933645 801165464430691439975117)
            ·
              refine ⟨300437049161509289990669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 801165464430691439975117 300437049161509289990669)
              ·
                refine ⟨112663893435565983746501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300437049161509289990669 112663893435565983746501)
                ·
                  rfl

theorem cell19_370258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_370258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370258 prefixEnd_370258 := by exact prefixLift 370258
  have htrace : WordTrace (prefixWord ++ tailWord_370258) baseStart_370258 baseEnd_370258 := by
    simpa [prefixWord, tailWord_370258, baseEnd_370258] using wordTrace_append hprefix tailTrace_370258
  have hstable : (prefixWord ++ tailWord_370258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370258).length < 2 ^ (prefixWord ++ tailWord_370258).sum := by decide
  have hdescent : baseEnd_370258 < baseStart_370258 := by decide
  rcases family_descends (prefixWord ++ tailWord_370258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370300 : List Nat := [2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_370300 : Nat := 118140960795 + 370300 * 2 ^ 59
def prefixEnd_370300 : Nat := 4983230072969 + 3 ^ 40 * 370300 * 2
def baseEnd_370300 : Nat := 112676673398522330813053

theorem tailTrace_370300 : CollatzResearch.WordTrace tailWord_370300 prefixEnd_370300 112676673398522330813053 := by
  unfold tailWord_370300
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752975279236908525070177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9003967038982544700093569 6752975279236908525070177)
  ·
    refine ⟨5064731459427681393802633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6752975279236908525070177 5064731459427681393802633)
    ·
      refine ⟨3798548594570761045351975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5064731459427681393802633 3798548594570761045351975)
      ·
        refine ⟨5697822891856141568027963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3798548594570761045351975 5697822891856141568027963)
        ·
          refine ⟨8546734337784212352041945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697822891856141568027963 8546734337784212352041945)
          ·
            refine ⟨6410050753338159264031459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8546734337784212352041945 6410050753338159264031459)
            ·
              refine ⟨9615076130007238896047189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410050753338159264031459 9615076130007238896047189)
              ·
                refine ⟨112676673398522330813053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9615076130007238896047189 112676673398522330813053)
                ·
                  rfl

theorem cell19_370300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_370300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370300 prefixEnd_370300 := by exact prefixLift 370300
  have htrace : WordTrace (prefixWord ++ tailWord_370300) baseStart_370300 baseEnd_370300 := by
    simpa [prefixWord, tailWord_370300, baseEnd_370300] using wordTrace_append hprefix tailTrace_370300
  have hstable : (prefixWord ++ tailWord_370300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370300).length < 2 ^ (prefixWord ++ tailWord_370300).sum := by decide
  have hdescent : baseEnd_370300 < baseStart_370300 := by decide
  rcases family_descends (prefixWord ++ tailWord_370300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370334 : List Nat := [4, 3, 1, 1, 1, 4, 5]
def baseStart_370334 : Nat := 118140960795 + 370334 * 2 ^ 59
def prefixEnd_370334 : Nat := 4983230072969 + 3 ^ 40 * 370334 * 2
def baseEnd_370334 : Nat := 37562339694273442019135

theorem tailTrace_370334 : CollatzResearch.WordTrace tailWord_370334 prefixEnd_370334 37562339694273442019135 := by
  unfold tailWord_370334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1688398830043830107109757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9004793760233760571252037 1688398830043830107109757)
  ·
    refine ⟨633149561266436290166159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1688398830043830107109757 633149561266436290166159)
    ·
      refine ⟨949724341899654435249239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633149561266436290166159 949724341899654435249239)
      ·
        refine ⟨1424586512849481652873859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949724341899654435249239 1424586512849481652873859)
        ·
          refine ⟨2136879769274222479310789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424586512849481652873859 2136879769274222479310789)
          ·
            refine ⟨400664956738916714870773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2136879769274222479310789 400664956738916714870773)
            ·
              refine ⟨37562339694273442019135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 400664956738916714870773 37562339694273442019135)
              ·
                rfl

theorem cell19_370334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_370334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370334 prefixEnd_370334 := by exact prefixLift 370334
  have htrace : WordTrace (prefixWord ++ tailWord_370334) baseStart_370334 baseEnd_370334 := by
    simpa [prefixWord, tailWord_370334, baseEnd_370334] using wordTrace_append hprefix tailTrace_370334
  have hstable : (prefixWord ++ tailWord_370334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370334).length < 2 ^ (prefixWord ++ tailWord_370334).sum := by decide
  have hdescent : baseEnd_370334 < baseStart_370334 := by decide
  rcases family_descends (prefixWord ++ tailWord_370334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370336 : List Nat := [2, 1, 1, 4, 3, 3, 5]
def baseStart_370336 : Nat := 118140960795 + 370336 * 2 ^ 59
def prefixEnd_370336 : Nat := 4983230072969 + 3 ^ 40 * 370336 * 2
def baseEnd_370336 : Nat := 37562542550828304670985

theorem tailTrace_370336 : CollatzResearch.WordTrace tailWord_370336 prefixEnd_370336 37562542550828304670985 := by
  unfold tailWord_370336
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753631793171697599225431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9004842390895596798967241 6753631793171697599225431)
  ·
    refine ⟨10130447689757546398838147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6753631793171697599225431 10130447689757546398838147)
    ·
      refine ⟨15195671534636319598257221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10130447689757546398838147 15195671534636319598257221)
      ·
        refine ⟨2849188412744309924673229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15195671534636319598257221 2849188412744309924673229)
        ·
          refine ⟨1068445654779116221752461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2849188412744309924673229 1068445654779116221752461)
          ·
            refine ⟨400667120542168583157173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1068445654779116221752461 400667120542168583157173)
            ·
              refine ⟨37562542550828304670985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 400667120542168583157173 37562542550828304670985)
              ·
                rfl

theorem cell19_370336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_370336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370336 prefixEnd_370336 := by exact prefixLift 370336
  have htrace : WordTrace (prefixWord ++ tailWord_370336) baseStart_370336 baseEnd_370336 := by
    simpa [prefixWord, tailWord_370336, baseEnd_370336] using wordTrace_append hprefix tailTrace_370336
  have hstable : (prefixWord ++ tailWord_370336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370336).length < 2 ^ (prefixWord ++ tailWord_370336).sum := by decide
  have hdescent : baseEnd_370336 < baseStart_370336 := by decide
  rcases family_descends (prefixWord ++ tailWord_370336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370376 : List Nat := [2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_370376 : Nat := 118140960795 + 370376 * 2 ^ 59
def prefixEnd_370376 : Nat := 4983230072969 + 3 ^ 40 * 370376 * 2
def baseEnd_370376 : Nat := 112699799045776673123957

theorem tailTrace_370376 : CollatzResearch.WordTrace tailWord_370376 prefixEnd_370376 112699799045776673123957 := by
  unfold tailWord_370376
  simp only [CollatzResearch.WordTrace]
  refine ⟨6754361253099241014953491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9005815004132321353271321 6754361253099241014953491)
  ·
    refine ⟨10131541879648861522430237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6754361253099241014953491 10131541879648861522430237)
    ·
      refine ⟨3799328204868323070911339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10131541879648861522430237 3799328204868323070911339)
      ·
        refine ⟨5698992307302484606367009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3799328204868323070911339 5698992307302484606367009)
        ·
          refine ⟨4274244230476863454775257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5698992307302484606367009 4274244230476863454775257)
          ·
            refine ⟨3205683172857647591081443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274244230476863454775257 3205683172857647591081443)
            ·
              refine ⟨4808524759286471386622165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205683172857647591081443 4808524759286471386622165)
              ·
                refine ⟨112699799045776673123957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4808524759286471386622165 112699799045776673123957)
                ·
                  rfl

theorem cell19_370376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_370376 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370376 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370376 prefixEnd_370376 := by exact prefixLift 370376
  have htrace : WordTrace (prefixWord ++ tailWord_370376) baseStart_370376 baseEnd_370376 := by
    simpa [prefixWord, tailWord_370376, baseEnd_370376] using wordTrace_append hprefix tailTrace_370376
  have hstable : (prefixWord ++ tailWord_370376).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370376).length < 2 ^ (prefixWord ++ tailWord_370376).sum := by decide
  have hdescent : baseEnd_370376 < baseStart_370376 := by decide
  rcases family_descends (prefixWord ++ tailWord_370376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370433 : List Nat := [1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_370433 : Nat := 118140960795 + 370433 * 2 ^ 59
def prefixEnd_370433 : Nat := 4983230072969 + 3 ^ 40 * 370433 * 2
def baseEnd_370433 : Nat := 112717143281217429857135

theorem tailTrace_370433 : CollatzResearch.WordTrace tailWord_370433 prefixEnd_370433 112717143281217429857135 := by
  unfold tailWord_370433
  simp only [CollatzResearch.WordTrace]
  refine ⟨13510801466991980764731953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9007200977994653843154635 13510801466991980764731953)
  ·
    refine ⟨10133101100243985573548965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13510801466991980764731953 10133101100243985573548965)
    ·
      refine ⟨1899956456295747295040431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10133101100243985573548965 1899956456295747295040431)
      ·
        refine ⟨2849934684443620942560647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899956456295747295040431 2849934684443620942560647)
        ·
          refine ⟨4274902026665431413840971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849934684443620942560647 4274902026665431413840971)
          ·
            refine ⟨6412353039998147120761457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274902026665431413840971 6412353039998147120761457)
            ·
              refine ⟨4809264779998610340571093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6412353039998147120761457 4809264779998610340571093)
              ·
                refine ⟨112717143281217429857135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4809264779998610340571093 112717143281217429857135)
                ·
                  rfl

theorem cell19_370433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_370433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370433 prefixEnd_370433 := by exact prefixLift 370433
  have htrace : WordTrace (prefixWord ++ tailWord_370433) baseStart_370433 baseEnd_370433 := by
    simpa [prefixWord, tailWord_370433, baseEnd_370433] using wordTrace_append hprefix tailTrace_370433
  have hstable : (prefixWord ++ tailWord_370433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370433).length < 2 ^ (prefixWord ++ tailWord_370433).sum := by decide
  have hdescent : baseEnd_370433 < baseStart_370433 := by decide
  rcases family_descends (prefixWord ++ tailWord_370433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370484 : List Nat := [2, 5, 1, 1, 2, 3, 2, 3]
def baseStart_370484 : Nat := 118140960795 + 370484 * 2 ^ 59
def prefixEnd_370484 : Nat := 4983230072969 + 3 ^ 40 * 370484 * 2
def baseEnd_370484 : Nat := 112732661807664422723663

theorem tailTrace_370484 : CollatzResearch.WordTrace tailWord_370484 prefixEnd_370484 112732661807664422723663 := by
  unfold tailWord_370484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6756330794903608237419253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9008441059871477649892337 6756330794903608237419253)
  ·
    refine ⟨633406012022213272258055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6756330794903608237419253 633406012022213272258055)
    ·
      refine ⟨950109018033319908387083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633406012022213272258055 950109018033319908387083)
      ·
        refine ⟨1425163527049979862580625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950109018033319908387083 1425163527049979862580625)
        ·
          refine ⟨1068872645287484896935469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425163527049979862580625 1068872645287484896935469)
          ·
            refine ⟨400827241982806836350801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1068872645287484896935469 400827241982806836350801)
            ·
              refine ⟨300620431487105127263101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400827241982806836350801 300620431487105127263101)
              ·
                refine ⟨112732661807664422723663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300620431487105127263101 112732661807664422723663)
                ·
                  rfl

theorem cell19_370484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_370484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370484 prefixEnd_370484 := by exact prefixLift 370484
  have htrace : WordTrace (prefixWord ++ tailWord_370484) baseStart_370484 baseEnd_370484 := by
    simpa [prefixWord, tailWord_370484, baseEnd_370484] using wordTrace_append hprefix tailTrace_370484
  have hstable : (prefixWord ++ tailWord_370484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370484).length < 2 ^ (prefixWord ++ tailWord_370484).sum := by decide
  have hdescent : baseEnd_370484 < baseStart_370484 := by decide
  rcases family_descends (prefixWord ++ tailWord_370484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370486 : List Nat := [5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_370486 : Nat := 118140960795 + 370486 * 2 ^ 59
def prefixEnd_370486 : Nat := 4983230072969 + 3 ^ 40 * 370486 * 2
def baseEnd_370486 : Nat := 112733270377329010679213

theorem tailTrace_370486 : CollatzResearch.WordTrace tailWord_370486 prefixEnd_370486 112733270377329010679213 := by
  unfold tailWord_370486
  simp only [CollatzResearch.WordTrace]
  refine ⟨844545908487498176025707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9008489690533313877607541 844545908487498176025707)
  ·
    refine ⟨1266818862731247264038561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 844545908487498176025707 1266818862731247264038561)
    ·
      refine ⟨950114147048435448028921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1266818862731247264038561 950114147048435448028921)
      ·
        refine ⟨712585610286326586021691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 950114147048435448028921 712585610286326586021691)
        ·
          refine ⟨1068878415429489879032537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712585610286326586021691 1068878415429489879032537)
          ·
            refine ⟨801658811572117409274403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068878415429489879032537 801658811572117409274403)
            ·
              refine ⟨1202488217358176113911605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801658811572117409274403 1202488217358176113911605)
              ·
                refine ⟨112733270377329010679213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1202488217358176113911605 112733270377329010679213)
                ·
                  rfl

theorem cell19_370486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_370486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370486 prefixEnd_370486 := by exact prefixLift 370486
  have htrace : WordTrace (prefixWord ++ tailWord_370486) baseStart_370486 baseEnd_370486 := by
    simpa [prefixWord, tailWord_370486, baseEnd_370486] using wordTrace_append hprefix tailTrace_370486
  have hstable : (prefixWord ++ tailWord_370486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370486).length < 2 ^ (prefixWord ++ tailWord_370486).sum := by decide
  have hdescent : baseEnd_370486 < baseStart_370486 := by decide
  rcases family_descends (prefixWord ++ tailWord_370486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370488 : List Nat := [2, 1, 2, 1, 3, 3, 4, 3]
def baseStart_370488 : Nat := 118140960795 + 370488 * 2 ^ 59
def prefixEnd_370488 : Nat := 4983230072969 + 3 ^ 40 * 370488 * 2
def baseEnd_370488 : Nat := 112733878946993598634763

theorem tailTrace_370488 : CollatzResearch.WordTrace tailWord_370488 prefixEnd_370488 112733878946993598634763 := by
  unfold tailWord_370488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6756403740896362578992059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9008538321195150105322745 6756403740896362578992059)
  ·
    refine ⟨10134605611344543868488089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6756403740896362578992059 10134605611344543868488089)
    ·
      refine ⟨7600954208508407901366067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10134605611344543868488089 7600954208508407901366067)
      ·
        refine ⟨11401431312762611852049101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7600954208508407901366067 11401431312762611852049101)
        ·
          refine ⟨4275536742285979444518413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11401431312762611852049101 4275536742285979444518413)
          ·
            refine ⟨1603326278357242291694405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4275536742285979444518413 1603326278357242291694405)
            ·
              refine ⟨300623677191982929692701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1603326278357242291694405 300623677191982929692701)
              ·
                refine ⟨112733878946993598634763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300623677191982929692701 112733878946993598634763)
                ·
                  rfl

theorem cell19_370488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_370488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370488 prefixEnd_370488 := by exact prefixLift 370488
  have htrace : WordTrace (prefixWord ++ tailWord_370488) baseStart_370488 baseEnd_370488 := by
    simpa [prefixWord, tailWord_370488, baseEnd_370488] using wordTrace_append hprefix tailTrace_370488
  have hstable : (prefixWord ++ tailWord_370488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370488).length < 2 ^ (prefixWord ++ tailWord_370488).sum := by decide
  have hdescent : baseEnd_370488 < baseStart_370488 := by decide
  rcases family_descends (prefixWord ++ tailWord_370488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370524 : List Nat := [2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_370524 : Nat := 118140960795 + 370524 * 2 ^ 59
def prefixEnd_370524 : Nat := 4983230072969 + 3 ^ 40 * 370524 * 2
def baseEnd_370524 : Nat := 112744833200956181834665

theorem tailTrace_370524 : CollatzResearch.WordTrace tailWord_370524 prefixEnd_370524 112744833200956181834665 := by
  unfold tailWord_370524
  simp only [CollatzResearch.WordTrace]
  refine ⟨6757060254831151653147313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9009413673108202204196417 6757060254831151653147313)
  ·
    refine ⟨5067795191123363739860485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6757060254831151653147313 5067795191123363739860485)
    ·
      refine ⟨950211598335630701223841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5067795191123363739860485 950211598335630701223841)
      ·
        refine ⟨712658698751723025917881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 950211598335630701223841 712658698751723025917881)
        ·
          refine ⟨534494024063792269438411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712658698751723025917881 534494024063792269438411)
          ·
            refine ⟨801741036095688404157617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534494024063792269438411 801741036095688404157617)
            ·
              refine ⟨601305777071766303118213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801741036095688404157617 601305777071766303118213)
              ·
                refine ⟨112744833200956181834665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601305777071766303118213 112744833200956181834665)
                ·
                  rfl

theorem cell19_370524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_370524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370524 prefixEnd_370524 := by exact prefixLift 370524
  have htrace : WordTrace (prefixWord ++ tailWord_370524) baseStart_370524 baseEnd_370524 := by
    simpa [prefixWord, tailWord_370524, baseEnd_370524] using wordTrace_append hprefix tailTrace_370524
  have hstable : (prefixWord ++ tailWord_370524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370524).length < 2 ^ (prefixWord ++ tailWord_370524).sum := by decide
  have hdescent : baseEnd_370524 < baseStart_370524 := by decide
  rcases family_descends (prefixWord ++ tailWord_370524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370528 : List Nat := [2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_370528 : Nat := 118140960795 + 370528 * 2 ^ 59
def prefixEnd_370528 : Nat := 4983230072969 + 3 ^ 40 * 370528 * 2
def baseEnd_370528 : Nat := 112746050340285357745765

theorem tailTrace_370528 : CollatzResearch.WordTrace tailWord_370528 prefixEnd_370528 112746050340285357745765 := by
  unfold tailWord_370528
  simp only [CollatzResearch.WordTrace]
  refine ⟨6757133200823905994720119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9009510934431874659626825 6757133200823905994720119)
  ·
    refine ⟨10135699801235858992080179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6757133200823905994720119 10135699801235858992080179)
    ·
      refine ⟨15203549701853788488120269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10135699801235858992080179 15203549701853788488120269)
      ·
        refine ⟨5701331138195170683045101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15203549701853788488120269 5701331138195170683045101)
        ·
          refine ⟨2137999176823189006141913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5701331138195170683045101 2137999176823189006141913)
          ·
            refine ⟨1603499382617391754606435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2137999176823189006141913 1603499382617391754606435)
            ·
              refine ⟨2405249073926087631909653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603499382617391754606435 2405249073926087631909653)
              ·
                refine ⟨112746050340285357745765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2405249073926087631909653 112746050340285357745765)
                ·
                  rfl

theorem cell19_370528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_370528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370528 prefixEnd_370528 := by exact prefixLift 370528
  have htrace : WordTrace (prefixWord ++ tailWord_370528) baseStart_370528 baseEnd_370528 := by
    simpa [prefixWord, tailWord_370528, baseEnd_370528] using wordTrace_append hprefix tailTrace_370528
  have hstable : (prefixWord ++ tailWord_370528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370528).length < 2 ^ (prefixWord ++ tailWord_370528).sum := by decide
  have hdescent : baseEnd_370528 < baseStart_370528 := by decide
  rcases family_descends (prefixWord ++ tailWord_370528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370583 : List Nat := [1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_370583 : Nat := 118140960795 + 370583 * 2 ^ 59
def prefixEnd_370583 : Nat := 4983230072969 + 3 ^ 40 * 370583 * 2
def baseEnd_370583 : Nat := 112762786006061526523393

theorem tailTrace_370583 : CollatzResearch.WordTrace tailWord_370583 prefixEnd_370583 112762786006061526523393 := by
  unfold tailWord_370583
  simp only [CollatzResearch.WordTrace]
  refine ⟨13516272416448556382692403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9010848277632370921794935 13516272416448556382692403)
  ·
    refine ⟨20274408624672834574038605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13516272416448556382692403 20274408624672834574038605)
    ·
      refine ⟨7602903234252312965264477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20274408624672834574038605 7602903234252312965264477)
      ·
        refine ⟨2851088712844617361974179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7602903234252312965264477 2851088712844617361974179)
        ·
          refine ⟨4276633069266926042961269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851088712844617361974179 4276633069266926042961269)
          ·
            refine ⟨400934350243774316527619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4276633069266926042961269 400934350243774316527619)
            ·
              refine ⟨601401525365661474791429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400934350243774316527619 601401525365661474791429)
              ·
                refine ⟨112762786006061526523393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601401525365661474791429 112762786006061526523393)
                ·
                  rfl

theorem cell19_370583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_370583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370583 prefixEnd_370583 := by exact prefixLift 370583
  have htrace : WordTrace (prefixWord ++ tailWord_370583) baseStart_370583 baseEnd_370583 := by
    simpa [prefixWord, tailWord_370583, baseEnd_370583] using wordTrace_append hprefix tailTrace_370583
  have hstable : (prefixWord ++ tailWord_370583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370583).length < 2 ^ (prefixWord ++ tailWord_370583).sum := by decide
  have hdescent : baseEnd_370583 < baseStart_370583 := by decide
  rcases family_descends (prefixWord ++ tailWord_370583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370585 : List Nat := [1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_370585 : Nat := 118140960795 + 370585 * 2 ^ 59
def prefixEnd_370585 : Nat := 4983230072969 + 3 ^ 40 * 370585 * 2
def baseEnd_370585 : Nat := 112763394575726114478943

theorem tailTrace_370585 : CollatzResearch.WordTrace tailWord_370585 prefixEnd_370585 112763394575726114478943 := by
  unfold tailWord_370585
  simp only [CollatzResearch.WordTrace]
  refine ⟨13516345362441310724265209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9010896908294207149510139 13516345362441310724265209)
  ·
    refine ⟨10137259021830983043198907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13516345362441310724265209 10137259021830983043198907)
    ·
      refine ⟨15205888532746474564798361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10137259021830983043198907 15205888532746474564798361)
      ·
        refine ⟨11404416399559855923598771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15205888532746474564798361 11404416399559855923598771)
        ·
          refine ⟨17106624599339783885398157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11404416399559855923598771 17106624599339783885398157)
          ·
            refine ⟨6414984224752418957024309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17106624599339783885398157 6414984224752418957024309)
            ·
              refine ⟨601404771070539277221029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6414984224752418957024309 601404771070539277221029)
              ·
                refine ⟨112763394575726114478943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601404771070539277221029 112763394575726114478943)
                ·
                  rfl

theorem cell19_370585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_370585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370585 prefixEnd_370585 := by exact prefixLift 370585
  have htrace : WordTrace (prefixWord ++ tailWord_370585) baseStart_370585 baseEnd_370585 := by
    simpa [prefixWord, tailWord_370585, baseEnd_370585] using wordTrace_append hprefix tailTrace_370585
  have hstable : (prefixWord ++ tailWord_370585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370585).length < 2 ^ (prefixWord ++ tailWord_370585).sum := by decide
  have hdescent : baseEnd_370585 < baseStart_370585 := by decide
  rcases family_descends (prefixWord ++ tailWord_370585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370659 : List Nat := [1, 1, 1, 6, 1, 2, 4, 3]
def baseStart_370659 : Nat := 118140960795 + 370659 * 2 ^ 59
def prefixEnd_370659 : Nat := 4983230072969 + 3 ^ 40 * 370659 * 2
def baseEnd_370659 : Nat := 112785911653315868834297

theorem tailTrace_370659 : CollatzResearch.WordTrace tailWord_370659 prefixEnd_370659 112785911653315868834297 := by
  unfold tailWord_370659
  simp only [CollatzResearch.WordTrace]
  refine ⟨13519044364173221362459031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9012696242782147574972687 13519044364173221362459031)
  ·
    refine ⟨20278566546259832043688547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13519044364173221362459031 20278566546259832043688547)
    ·
      refine ⟨30417849819389748065532821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20278566546259832043688547 30417849819389748065532821)
      ·
        refine ⟨1425836710283894440571851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30417849819389748065532821 1425836710283894440571851)
        ·
          refine ⟨2138755065425841660857777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1425836710283894440571851 2138755065425841660857777)
          ·
            refine ⟨1604066299069381245643333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2138755065425841660857777 1604066299069381245643333)
            ·
              refine ⟨300762431075508983558125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1604066299069381245643333 300762431075508983558125)
              ·
                refine ⟨112785911653315868834297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300762431075508983558125 112785911653315868834297)
                ·
                  rfl

theorem cell19_370659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_370659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370659 prefixEnd_370659 := by exact prefixLift 370659
  have htrace : WordTrace (prefixWord ++ tailWord_370659) baseStart_370659 baseEnd_370659 := by
    simpa [prefixWord, tailWord_370659, baseEnd_370659] using wordTrace_append hprefix tailTrace_370659
  have hstable : (prefixWord ++ tailWord_370659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370659).length < 2 ^ (prefixWord ++ tailWord_370659).sum := by decide
  have hdescent : baseEnd_370659 < baseStart_370659 := by decide
  rcases family_descends (prefixWord ++ tailWord_370659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370699 : List Nat := [1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_370699 : Nat := 118140960795 + 370699 * 2 ^ 59
def prefixEnd_370699 : Nat := 4983230072969 + 3 ^ 40 * 370699 * 2
def baseEnd_370699 : Nat := 112798083046607627945299

theorem tailTrace_370699 : CollatzResearch.WordTrace tailWord_370699 prefixEnd_370699 112798083046607627945299 := by
  unfold tailWord_370699
  simp only [CollatzResearch.WordTrace]
  refine ⟨13520503284028308193915151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9013668856018872129276767 13520503284028308193915151)
  ·
    refine ⟨20280754926042462290872727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13520503284028308193915151 20280754926042462290872727)
    ·
      refine ⟨30421132389063693436309091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20280754926042462290872727 30421132389063693436309091)
      ·
        refine ⟨45631698583595540154463637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30421132389063693436309091 45631698583595540154463637)
        ·
          refine ⟨2138985871106040944740483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45631698583595540154463637 2138985871106040944740483)
          ·
            refine ⟨3208478806659061417110725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138985871106040944740483 3208478806659061417110725)
            ·
              refine ⟨601589776248574015708261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3208478806659061417110725 601589776248574015708261)
              ·
                refine ⟨112798083046607627945299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601589776248574015708261 112798083046607627945299)
                ·
                  rfl

theorem cell19_370699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_370699 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370699 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370699 prefixEnd_370699 := by exact prefixLift 370699
  have htrace : WordTrace (prefixWord ++ tailWord_370699) baseStart_370699 baseEnd_370699 := by
    simpa [prefixWord, tailWord_370699, baseEnd_370699] using wordTrace_append hprefix tailTrace_370699
  have hstable : (prefixWord ++ tailWord_370699).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370699).length < 2 ^ (prefixWord ++ tailWord_370699).sum := by decide
  have hdescent : baseEnd_370699 < baseStart_370699 := by decide
  rcases family_descends (prefixWord ++ tailWord_370699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370750 : List Nat := [4, 2, 1, 3, 3, 1, 1, 4]
def baseStart_370750 : Nat := 118140960795 + 370750 * 2 ^ 59
def prefixEnd_370750 : Nat := 4983230072969 + 3 ^ 40 * 370750 * 2
def baseEnd_370750 : Nat := 112813601573054620811827

theorem tailTrace_370750 : CollatzResearch.WordTrace tailWord_370750 prefixEnd_370750 112813601573054620811827 := by
  unfold tailWord_370750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690295425855442988002713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9014908937895695936014469 1690295425855442988002713)
  ·
    refine ⟨1267721569391582241002035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1690295425855442988002713 1267721569391582241002035)
    ·
      refine ⟨1901582354087373361503053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267721569391582241002035 1901582354087373361503053)
      ·
        refine ⟨713093382782765010563645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1901582354087373361503053 713093382782765010563645)
        ·
          refine ⟨267410018543536878961367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 713093382782765010563645 267410018543536878961367)
          ·
            refine ⟨401115027815305318442051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267410018543536878961367 401115027815305318442051)
            ·
              refine ⟨601672541722957977663077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401115027815305318442051 601672541722957977663077)
              ·
                refine ⟨112813601573054620811827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601672541722957977663077 112813601573054620811827)
                ·
                  rfl

theorem cell19_370750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_370750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370750 prefixEnd_370750 := by exact prefixLift 370750
  have htrace : WordTrace (prefixWord ++ tailWord_370750) baseStart_370750 baseEnd_370750 := by
    simpa [prefixWord, tailWord_370750, baseEnd_370750] using wordTrace_append hprefix tailTrace_370750
  have hstable : (prefixWord ++ tailWord_370750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370750).length < 2 ^ (prefixWord ++ tailWord_370750).sum := by decide
  have hdescent : baseEnd_370750 < baseStart_370750 := by decide
  rcases family_descends (prefixWord ++ tailWord_370750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370773 : List Nat := [1, 3, 2, 2, 1, 4, 3, 3]
def baseStart_370773 : Nat := 118140960795 + 370773 * 2 ^ 59
def prefixEnd_370773 : Nat := 4983230072969 + 3 ^ 40 * 370773 * 2
def baseEnd_370773 : Nat := 112820600124197382300653

theorem tailTrace_370773 : CollatzResearch.WordTrace tailWord_370773 prefixEnd_370773 112820600124197382300653 := by
  unfold tailWord_370773
  simp only [CollatzResearch.WordTrace]
  refine ⟨13523202285760218832108973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9015468190506812554739315 13523202285760218832108973)
  ·
    refine ⟨5071200857160082062040865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13523202285760218832108973 5071200857160082062040865)
    ·
      refine ⟨3803400642870061546530649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5071200857160082062040865 3803400642870061546530649)
      ·
        refine ⟨2852550482152546159897987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3803400642870061546530649 2852550482152546159897987)
        ·
          refine ⟨4278825723228819239846981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852550482152546159897987 4278825723228819239846981)
          ·
            refine ⟨802279823105403607471309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4278825723228819239846981 802279823105403607471309)
            ·
              refine ⟨300854933664526352801741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 802279823105403607471309 300854933664526352801741)
              ·
                refine ⟨112820600124197382300653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300854933664526352801741 112820600124197382300653)
                ·
                  rfl

theorem cell19_370773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_370773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370773 prefixEnd_370773 := by exact prefixLift 370773
  have htrace : WordTrace (prefixWord ++ tailWord_370773) baseStart_370773 baseEnd_370773 := by
    simpa [prefixWord, tailWord_370773, baseEnd_370773] using wordTrace_append hprefix tailTrace_370773
  have hstable : (prefixWord ++ tailWord_370773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370773).length < 2 ^ (prefixWord ++ tailWord_370773).sum := by decide
  have hdescent : baseEnd_370773 < baseStart_370773 := by decide
  rcases family_descends (prefixWord ++ tailWord_370773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370830 : List Nat := [4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_370830 : Nat := 118140960795 + 370830 * 2 ^ 59
def prefixEnd_370830 : Nat := 4983230072969 + 3 ^ 40 * 370830 * 2
def baseEnd_370830 : Nat := 112837944359638139033831

theorem tailTrace_370830 : CollatzResearch.WordTrace tailWord_370830 prefixEnd_370830 112837944359638139033831 := by
  unfold tailWord_370830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690660155819214695866743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9016854164369145044622629 1690660155819214695866743)
  ·
    refine ⟨2535990233728822043800115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1690660155819214695866743 2535990233728822043800115)
    ·
      refine ⟨3803985350593233065700173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2535990233728822043800115 3803985350593233065700173)
      ·
        refine ⟨1426494506472462399637565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3803985350593233065700173 1426494506472462399637565)
        ·
          refine ⟨534935439927173399864087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1426494506472462399637565 534935439927173399864087)
          ·
            refine ⟨802403159890760099796131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534935439927173399864087 802403159890760099796131)
            ·
              refine ⟨1203604739836140149694197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802403159890760099796131 1203604739836140149694197)
              ·
                refine ⟨112837944359638139033831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1203604739836140149694197 112837944359638139033831)
                ·
                  rfl

theorem cell19_370830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_370830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370830 prefixEnd_370830 := by exact prefixLift 370830
  have htrace : WordTrace (prefixWord ++ tailWord_370830) baseStart_370830 baseEnd_370830 := by
    simpa [prefixWord, tailWord_370830, baseEnd_370830] using wordTrace_append hprefix tailTrace_370830
  have hstable : (prefixWord ++ tailWord_370830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370830).length < 2 ^ (prefixWord ++ tailWord_370830).sum := by decide
  have hdescent : baseEnd_370830 < baseStart_370830 := by decide
  rcases family_descends (prefixWord ++ tailWord_370830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370891 : List Nat := [1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_370891 : Nat := 118140960795 + 370891 * 2 ^ 59
def prefixEnd_370891 : Nat := 4983230072969 + 3 ^ 40 * 370891 * 2
def baseEnd_370891 : Nat := 112856505734408071678109

theorem tailTrace_370891 : CollatzResearch.WordTrace tailWord_370891 prefixEnd_370891 112856505734408071678109 := by
  unfold tailWord_370891
  simp only [CollatzResearch.WordTrace]
  refine ⟨13527506099332724984904527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9018337399555149989936351 13527506099332724984904527)
  ·
    refine ⟨20291259148999087477356791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13527506099332724984904527 20291259148999087477356791)
    ·
      refine ⟨30436888723498631216035187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20291259148999087477356791 30436888723498631216035187)
      ·
        refine ⟨45655333085247946824052781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30436888723498631216035187 45655333085247946824052781)
        ·
          refine ⟨17120749906967980059019793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45655333085247946824052781 17120749906967980059019793)
          ·
            refine ⟨12840562430225985044264845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17120749906967980059019793 12840562430225985044264845)
            ·
              refine ⟨4815210911334744391599317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12840562430225985044264845 4815210911334744391599317)
              ·
                refine ⟨112856505734408071678109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4815210911334744391599317 112856505734408071678109)
                ·
                  rfl

theorem cell19_370891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_370891 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370891 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370891 prefixEnd_370891 := by exact prefixLift 370891
  have htrace : WordTrace (prefixWord ++ tailWord_370891) baseStart_370891 baseEnd_370891 := by
    simpa [prefixWord, tailWord_370891, baseEnd_370891] using wordTrace_append hprefix tailTrace_370891
  have hstable : (prefixWord ++ tailWord_370891).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370891).length < 2 ^ (prefixWord ++ tailWord_370891).sum := by decide
  have hdescent : baseEnd_370891 < baseStart_370891 := by decide
  rcases family_descends (prefixWord ++ tailWord_370891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370910 : List Nat := [4, 15]
def baseStart_370910 : Nat := 118140960795 + 370910 * 2 ^ 59
def prefixEnd_370910 : Nat := 4983230072969 + 3 ^ 40 * 370910 * 2
def baseEnd_370910 : Nat := 154817952189604468115

theorem tailTrace_370910 : CollatzResearch.WordTrace tailWord_370910 prefixEnd_370910 154817952189604468115 := by
  unfold tailWord_370910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1691024885782986403730773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9018799390842594153230789 1691024885782986403730773)
  ·
    refine ⟨154817952189604468115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 15 1691024885782986403730773 154817952189604468115)
    ·
      rfl

theorem cell19_370910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 15].length) (baseStart_370910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370910 prefixEnd_370910 := by exact prefixLift 370910
  have htrace : WordTrace (prefixWord ++ tailWord_370910) baseStart_370910 baseEnd_370910 := by
    simpa [prefixWord, tailWord_370910, baseEnd_370910] using wordTrace_append hprefix tailTrace_370910
  have hstable : (prefixWord ++ tailWord_370910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370910).length < 2 ^ (prefixWord ++ tailWord_370910).sum := by decide
  have hdescent : baseEnd_370910 < baseStart_370910 := by decide
  rcases family_descends (prefixWord ++ tailWord_370910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370927 : List Nat := [1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_370927 : Nat := 118140960795 + 370927 * 2 ^ 59
def prefixEnd_370927 : Nat := 4983230072969 + 3 ^ 40 * 370927 * 2
def baseEnd_370927 : Nat := 112867459988370654878011

theorem tailTrace_370927 : CollatzResearch.WordTrace tailWord_370927 prefixEnd_370927 112867459988370654878011 := by
  unfold tailWord_370927
  simp only [CollatzResearch.WordTrace]
  refine ⟨13528819127202303133215035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9019212751468202088810023 13528819127202303133215035)
  ·
    refine ⟨20293228690803454699822553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13528819127202303133215035 20293228690803454699822553)
    ·
      refine ⟨15219921518102591024866915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20293228690803454699822553 15219921518102591024866915)
      ·
        refine ⟨22829882277153886537300373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15219921518102591024866915 22829882277153886537300373)
        ·
          refine ⟨1070150731741588431435955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22829882277153886537300373 1070150731741588431435955)
          ·
            refine ⟨1605226097612382647153933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070150731741588431435955 1605226097612382647153933)
            ·
              refine ⟨601959786604643492682725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1605226097612382647153933 601959786604643492682725)
              ·
                refine ⟨112867459988370654878011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601959786604643492682725 112867459988370654878011)
                ·
                  rfl

theorem cell19_370927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_370927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_370927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_370927 prefixEnd_370927 := by exact prefixLift 370927
  have htrace : WordTrace (prefixWord ++ tailWord_370927) baseStart_370927 baseEnd_370927 := by
    simpa [prefixWord, tailWord_370927, baseEnd_370927] using wordTrace_append hprefix tailTrace_370927
  have hstable : (prefixWord ++ tailWord_370927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370927).length < 2 ^ (prefixWord ++ tailWord_370927).sum := by decide
  have hdescent : baseEnd_370927 < baseStart_370927 := by decide
  rcases family_descends (prefixWord ++ tailWord_370927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371001 : List Nat := [1, 2, 1, 6, 1, 1, 4, 3]
def baseStart_371001 : Nat := 118140960795 + 371001 * 2 ^ 59
def prefixEnd_371001 : Nat := 4983230072969 + 3 ^ 40 * 371001 * 2
def baseEnd_371001 : Nat := 112889977065960409233365

theorem tailTrace_371001 : CollatzResearch.WordTrace tailWord_371001 prefixEnd_371001 112889977065960409233365 := by
  unfold tailWord_371001
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531518128934213771408857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9021012085956142514272571 13531518128934213771408857)
  ·
    refine ⟨10148638596700660328556643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13531518128934213771408857 10148638596700660328556643)
    ·
      refine ⟨15222957895050990492834965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10148638596700660328556643 15222957895050990492834965)
      ·
        refine ⟨713576151330515179351639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15222957895050990492834965 713576151330515179351639)
        ·
          refine ⟨1070364226995772769027459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713576151330515179351639 1070364226995772769027459)
          ·
            refine ⟨1605546340493659153541189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070364226995772769027459 1605546340493659153541189)
            ·
              refine ⟨301039938842561091288973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1605546340493659153541189 301039938842561091288973)
              ·
                refine ⟨112889977065960409233365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301039938842561091288973 112889977065960409233365)
                ·
                  rfl

theorem cell19_371001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_371001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371001 prefixEnd_371001 := by exact prefixLift 371001
  have htrace : WordTrace (prefixWord ++ tailWord_371001) baseStart_371001 baseEnd_371001 := by
    simpa [prefixWord, tailWord_371001, baseEnd_371001] using wordTrace_append hprefix tailTrace_371001
  have hstable : (prefixWord ++ tailWord_371001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371001).length < 2 ^ (prefixWord ++ tailWord_371001).sum := by decide
  have hdescent : baseEnd_371001 < baseStart_371001 := by decide
  rcases family_descends (prefixWord ++ tailWord_371001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371024 : List Nat := [2, 1, 1, 1, 1, 6, 7]
def baseStart_371024 : Nat := 118140960795 + 371024 * 2 ^ 59
def prefixEnd_371024 : Nat := 4983230072969 + 3 ^ 40 * 371024 * 2
def baseEnd_371024 : Nat := 37632325205701056907397

theorem tailTrace_371024 : CollatzResearch.WordTrace tailWord_371024 prefixEnd_371024 37632325205701056907397 := by
  unfold tailWord_371024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766178503925444349748063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9021571338567259132997417 6766178503925444349748063)
  ·
    refine ⟨10149267755888166524622095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6766178503925444349748063 10149267755888166524622095)
    ·
      refine ⟨15223901633832249786933143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10149267755888166524622095 15223901633832249786933143)
      ·
        refine ⟨22835852450748374680399715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15223901633832249786933143 22835852450748374680399715)
        ·
          refine ⟨34253778676122562020599573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22835852450748374680399715 34253778676122562020599573)
          ·
            refine ⟨1605645875443245094715605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34253778676122562020599573 1605645875443245094715605)
            ·
              refine ⟨37632325205701056907397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1605645875443245094715605 37632325205701056907397)
              ·
                rfl

theorem cell19_371024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_371024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371024 prefixEnd_371024 := by exact prefixLift 371024
  have htrace : WordTrace (prefixWord ++ tailWord_371024) baseStart_371024 baseEnd_371024 := by
    simpa [prefixWord, tailWord_371024, baseEnd_371024] using wordTrace_append hprefix tailTrace_371024
  have hstable : (prefixWord ++ tailWord_371024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371024).length < 2 ^ (prefixWord ++ tailWord_371024).sum := by decide
  have hdescent : baseEnd_371024 < baseStart_371024 := by decide
  rcases family_descends (prefixWord ++ tailWord_371024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371081 : List Nat := [1, 2, 1, 1, 6, 8]
def baseStart_371081 : Nat := 118140960795 + 371081 * 2 ^ 59
def prefixEnd_371081 : Nat := 4983230072969 + 3 ^ 40 * 371081 * 2
def baseEnd_371081 : Nat := 12546035539171547495041

theorem tailTrace_371081 : CollatzResearch.WordTrace tailWord_371081 prefixEnd_371081 12546035539171547495041 := by
  unfold tailWord_371081
  simp only [CollatzResearch.WordTrace]
  refine ⟨13534435968644387434321097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9022957312429591622880731 13534435968644387434321097)
  ·
    refine ⟨10150826976483290575740823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13534435968644387434321097 10150826976483290575740823)
    ·
      refine ⟨15226240464724935863611235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10150826976483290575740823 15226240464724935863611235)
      ·
        refine ⟨22839360697087403795416853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15226240464724935863611235 22839360697087403795416853)
        ·
          refine ⟨1070595032675972052910165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22839360697087403795416853 1070595032675972052910165)
          ·
            refine ⟨12546035539171547495041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1070595032675972052910165 12546035539171547495041)
            ·
              rfl

theorem cell19_371081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 8].length) (baseStart_371081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371081 prefixEnd_371081 := by exact prefixLift 371081
  have htrace : WordTrace (prefixWord ++ tailWord_371081) baseStart_371081 baseEnd_371081 := by
    simpa [prefixWord, tailWord_371081, baseEnd_371081] using wordTrace_append hprefix tailTrace_371081
  have hstable : (prefixWord ++ tailWord_371081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371081).length < 2 ^ (prefixWord ++ tailWord_371081).sum := by decide
  have hdescent : baseEnd_371081 < baseStart_371081 := by decide
  rcases family_descends (prefixWord ++ tailWord_371081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371096 : List Nat := [2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_371096 : Nat := 118140960795 + 371096 * 2 ^ 59
def prefixEnd_371096 : Nat := 4983230072969 + 3 ^ 40 * 371096 * 2
def baseEnd_371096 : Nat := 112918884125028337121995

theorem tailTrace_371096 : CollatzResearch.WordTrace tailWord_371096 prefixEnd_371096 112918884125028337121995 := by
  unfold tailWord_371096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6767491531795022498058571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9023322042393363330744761 6767491531795022498058571)
  ·
    refine ⟨10151237297692533747087857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6767491531795022498058571 10151237297692533747087857)
    ·
      refine ⟨7613427973269400310315893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10151237297692533747087857 7613427973269400310315893)
      ·
        refine ⟨713758872494006279092115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7613427973269400310315893 713758872494006279092115)
        ·
          refine ⟨1070638308741009418638173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713758872494006279092115 1070638308741009418638173)
          ·
            refine ⟨401489365777878531989315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1070638308741009418638173 401489365777878531989315)
            ·
              refine ⟨602234048666817797983973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401489365777878531989315 602234048666817797983973)
              ·
                refine ⟨112918884125028337121995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 602234048666817797983973 112918884125028337121995)
                ·
                  rfl

theorem cell19_371096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_371096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371096 prefixEnd_371096 := by exact prefixLift 371096
  have htrace : WordTrace (prefixWord ++ tailWord_371096) baseStart_371096 baseEnd_371096 := by
    simpa [prefixWord, tailWord_371096, baseEnd_371096] using wordTrace_append hprefix tailTrace_371096
  have hstable : (prefixWord ++ tailWord_371096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371096).length < 2 ^ (prefixWord ++ tailWord_371096).sum := by decide
  have hdescent : baseEnd_371096 < baseStart_371096 := by decide
  rcases family_descends (prefixWord ++ tailWord_371096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371098 : List Nat := [3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_371098 : Nat := 118140960795 + 371098 * 2 ^ 59
def prefixEnd_371098 : Nat := 4983230072969 + 3 ^ 40 * 371098 * 2
def baseEnd_371098 : Nat := 112919492694692925077545

theorem tailTrace_371098 : CollatzResearch.WordTrace tailWord_371098 prefixEnd_371098 112919492694692925077545 := by
  unfold tailWord_371098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3383764002395699834422487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9023370673055199558459965 3383764002395699834422487)
  ·
    refine ⟨5075646003593549751633731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3383764002395699834422487 5075646003593549751633731)
    ·
      refine ⟨7613469005390324627450597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5075646003593549751633731 7613469005390324627450597)
      ·
        refine ⟨1427525438510685867646987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7613469005390324627450597 1427525438510685867646987)
        ·
          refine ⟨2141288157766028801470481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427525438510685867646987 2141288157766028801470481)
          ·
            refine ⟨1605966118324521601102861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2141288157766028801470481 1605966118324521601102861)
            ·
              refine ⟨602237294371695600413573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1605966118324521601102861 602237294371695600413573)
              ·
                refine ⟨112919492694692925077545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 602237294371695600413573 112919492694692925077545)
                ·
                  rfl

theorem cell19_371098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_371098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371098 prefixEnd_371098 := by exact prefixLift 371098
  have htrace : WordTrace (prefixWord ++ tailWord_371098) baseStart_371098 baseEnd_371098 := by
    simpa [prefixWord, tailWord_371098, baseEnd_371098] using wordTrace_append hprefix tailTrace_371098
  have hstable : (prefixWord ++ tailWord_371098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371098).length < 2 ^ (prefixWord ++ tailWord_371098).sum := by decide
  have hdescent : baseEnd_371098 < baseStart_371098 := by decide
  rcases family_descends (prefixWord ++ tailWord_371098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371170 : List Nat := [3, 3, 3, 2, 1, 1, 1, 5]
def baseStart_371170 : Nat := 118140960795 + 371170 * 2 ^ 59
def prefixEnd_371170 : Nat := 4983230072969 + 3 ^ 40 * 371170 * 2
def baseEnd_371170 : Nat := 112941401202618091477349

theorem tailTrace_371170 : CollatzResearch.WordTrace tailWord_371170 prefixEnd_371170 112941401202618091477349 := by
  unfold tailWord_371170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384420516330488908577741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9025121376881303756207309 3384420516330488908577741)
  ·
    refine ⟨1269157693623933340716653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3384420516330488908577741 1269157693623933340716653)
    ·
      refine ⟨475934135108975002768745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1269157693623933340716653 475934135108975002768745)
      ·
        refine ⟨356950601331731252076559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475934135108975002768745 356950601331731252076559)
        ·
          refine ⟨535425901997596878114839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356950601331731252076559 535425901997596878114839)
          ·
            refine ⟨803138852996395317172259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535425901997596878114839 803138852996395317172259)
            ·
              refine ⟨1204708279494592975758389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803138852996395317172259 1204708279494592975758389)
              ·
                refine ⟨112941401202618091477349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1204708279494592975758389 112941401202618091477349)
                ·
                  rfl

theorem cell19_371170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_371170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_371170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_371170 prefixEnd_371170 := by exact prefixLift 371170
  have htrace : WordTrace (prefixWord ++ tailWord_371170) baseStart_371170 baseEnd_371170 := by
    simpa [prefixWord, tailWord_371170, baseEnd_371170] using wordTrace_append hprefix tailTrace_371170
  have hstable : (prefixWord ++ tailWord_371170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371170).length < 2 ^ (prefixWord ++ tailWord_371170).sum := by decide
  have hdescent : baseEnd_371170 < baseStart_371170 := by decide
  rcases family_descends (prefixWord ++ tailWord_371170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
