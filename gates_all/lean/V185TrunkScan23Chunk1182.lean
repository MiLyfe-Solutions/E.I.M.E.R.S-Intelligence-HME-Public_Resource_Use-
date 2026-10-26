import V185TrunkScan23Chunk1181

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7003084 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 1, 2, 3]
def baseStart_7003084 : Nat := 118140960795 + 7003084 * 2 ^ 59
def prefixEnd_7003084 : Nat := 4983230072969 + 3 ^ 40 * 7003084 * 2
def baseEnd_7003084 : Nat := 3595948155811183635343409

theorem tailTrace_7003084 : CollatzResearch.WordTrace tailWord_7003084 prefixEnd_7003084 3595948155811183635343409 := by
  unfold tailWord_7003084
  simp only [CollatzResearch.WordTrace]
  refine ⟨127711728680515087185688153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170282304907353449580917537 127711728680515087185688153)
  ·
    refine ⟨95783796510386315389266115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127711728680515087185688153 95783796510386315389266115)
    ·
      refine ⟨143675694765579473083899173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95783796510386315389266115 143675694765579473083899173)
      ·
        refine ⟨26939192768546151203231095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143675694765579473083899173 26939192768546151203231095)
        ·
          refine ⟨40408789152819226804846643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26939192768546151203231095 40408789152819226804846643)
          ·
            refine ⟨60613183729228840207269965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40408789152819226804846643 60613183729228840207269965)
            ·
              refine ⟨22729943898460815077726237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60613183729228840207269965 22729943898460815077726237)
              ·
                refine ⟨8523728961922805654147339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22729943898460815077726237 8523728961922805654147339)
                ·
                  refine ⟨12785593442884208481221009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523728961922805654147339 12785593442884208481221009)
                  ·
                    refine ⟨9589195082163156360915757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12785593442884208481221009 9589195082163156360915757)
                    ·
                      refine ⟨3595948155811183635343409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589195082163156360915757 3595948155811183635343409)
                      ·
                        rfl

theorem cell23_7003084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_7003084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003084 prefixEnd_7003084 := by exact prefixLift 7003084
  have htrace : WordTrace (prefixWord ++ tailWord_7003084) baseStart_7003084 baseEnd_7003084 := by
    simpa [prefixWord, tailWord_7003084, baseEnd_7003084] using wordTrace_append hprefix tailTrace_7003084
  have hstable : (prefixWord ++ tailWord_7003084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003084).length < 2 ^ (prefixWord ++ tailWord_7003084).sum := by decide
  have hdescent : baseEnd_7003084 < baseStart_7003084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003098 : List Nat := [3, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2]
def baseStart_7003098 : Nat := 118140960795 + 7003098 * 2 ^ 59
def prefixEnd_7003098 : Nat := 4983230072969 + 3 ^ 40 * 7003098 * 2
def baseEnd_7003098 : Nat := 3595955344540346580568345

theorem tailTrace_7003098 : CollatzResearch.WordTrace tailWord_7003098 prefixEnd_7003098 3595955344540346580568345 := by
  unfold tailWord_7003098
  simp only [CollatzResearch.WordTrace]
  refine ⟨63855991995744863690596487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170282645321986303174923965 63855991995744863690596487)
  ·
    refine ⟨95783987993617295535894731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63855991995744863690596487 95783987993617295535894731)
    ·
      refine ⟨143675981990425943303842097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95783987993617295535894731 143675981990425943303842097)
      ·
        refine ⟨107756986492819457477881573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143675981990425943303842097 107756986492819457477881573)
        ·
          refine ⟨20204434967403648277102795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107756986492819457477881573 20204434967403648277102795)
          ·
            refine ⟨30306652451105472415654193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20204434967403648277102795 30306652451105472415654193)
            ·
              refine ⟨22729989338329104311740645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30306652451105472415654193 22729989338329104311740645)
              ·
                refine ⟨4261873000936707058451371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22729989338329104311740645 4261873000936707058451371)
                ·
                  refine ⟨6392809501405060587677057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261873000936707058451371 6392809501405060587677057)
                  ·
                    refine ⟨4794607126053795440757793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6392809501405060587677057 4794607126053795440757793)
                    ·
                      refine ⟨3595955344540346580568345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794607126053795440757793 3595955344540346580568345)
                      ·
                        rfl

theorem cell23_7003098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_7003098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003098 prefixEnd_7003098 := by exact prefixLift 7003098
  have htrace : WordTrace (prefixWord ++ tailWord_7003098) baseStart_7003098 baseEnd_7003098 := by
    simpa [prefixWord, tailWord_7003098, baseEnd_7003098] using wordTrace_append hprefix tailTrace_7003098
  have hstable : (prefixWord ++ tailWord_7003098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003098).length < 2 ^ (prefixWord ++ tailWord_7003098).sum := by decide
  have hdescent : baseEnd_7003098 < baseStart_7003098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003114 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_7003114 : Nat := 118140960795 + 7003114 * 2 ^ 59
def prefixEnd_7003114 : Nat := 4983230072969 + 3 ^ 40 * 7003114 * 2
def baseEnd_7003114 : Nat := 3595963560230818517968271

theorem tailTrace_7003114 : CollatzResearch.WordTrace tailWord_7003114 prefixEnd_7003114 3595963560230818517968271 := by
  unfold tailWord_7003114
  simp only [CollatzResearch.WordTrace]
  refine ⟨63856137887730372373742099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170283034367280992996645597 63856137887730372373742099)
  ·
    refine ⟨95784206831595558560613149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63856137887730372373742099 95784206831595558560613149)
    ·
      refine ⟨35919077561848334460229931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95784206831595558560613149 35919077561848334460229931)
      ·
        refine ⟨53878616342772501690344897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35919077561848334460229931 53878616342772501690344897)
        ·
          refine ⟨40408962257079376267758673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53878616342772501690344897 40408962257079376267758673)
          ·
            refine ⟨30306721692809532200819005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40408962257079376267758673 30306721692809532200819005)
            ·
              refine ⟨11365020634803574575307127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30306721692809532200819005 11365020634803574575307127)
              ·
                refine ⟨17047530952205361862960691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11365020634803574575307127 17047530952205361862960691)
                ·
                  refine ⟨25571296428308042794441037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17047530952205361862960691 25571296428308042794441037)
                  ·
                    refine ⟨9589236160615516047915389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25571296428308042794441037 9589236160615516047915389)
                    ·
                      refine ⟨3595963560230818517968271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589236160615516047915389 3595963560230818517968271)
                      ·
                        rfl

theorem cell23_7003114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_7003114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003114 prefixEnd_7003114 := by exact prefixLift 7003114
  have htrace : WordTrace (prefixWord ++ tailWord_7003114) baseStart_7003114 baseEnd_7003114 := by
    simpa [prefixWord, tailWord_7003114, baseEnd_7003114] using wordTrace_append hprefix tailTrace_7003114
  have hstable : (prefixWord ++ tailWord_7003114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003114).length < 2 ^ (prefixWord ++ tailWord_7003114).sum := by decide
  have hdescent : baseEnd_7003114 < baseStart_7003114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003130 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_7003130 : Nat := 118140960795 + 7003130 * 2 ^ 59
def prefixEnd_7003130 : Nat := 4983230072969 + 3 ^ 40 * 7003130 * 2
def baseEnd_7003130 : Nat := 1198657258640430151789399

theorem tailTrace_7003130 : CollatzResearch.WordTrace tailWord_7003130 prefixEnd_7003130 1198657258640430151789399 := by
  unfold tailWord_7003130
  simp only [CollatzResearch.WordTrace]
  refine ⟨63856283779715881056887711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170283423412575682818367229 63856283779715881056887711)
  ·
    refine ⟨95784425669573821585331567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63856283779715881056887711 95784425669573821585331567)
    ·
      refine ⟨143676638504360732377997351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95784425669573821585331567 143676638504360732377997351)
      ·
        refine ⟨215514957756541098566996027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143676638504360732377997351 215514957756541098566996027)
        ·
          refine ⟨323272436634811647850494041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215514957756541098566996027 323272436634811647850494041)
          ·
            refine ⟨242454327476108735887870531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323272436634811647850494041 242454327476108735887870531)
            ·
              refine ⟨363681491214163103831805797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242454327476108735887870531 363681491214163103831805797)
              ·
                refine ⟨68190279602655581968463587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363681491214163103831805797 68190279602655581968463587)
                ·
                  refine ⟨102285419403983372952695381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68190279602655581968463587 102285419403983372952695381)
                  ·
                    refine ⟨1198657258640430151789399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102285419403983372952695381 1198657258640430151789399)
                    ·
                      rfl

theorem cell23_7003130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_7003130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003130 prefixEnd_7003130 := by exact prefixLift 7003130
  have htrace : WordTrace (prefixWord ++ tailWord_7003130) baseStart_7003130 baseEnd_7003130 := by
    simpa [prefixWord, tailWord_7003130, baseEnd_7003130] using wordTrace_append hprefix tailTrace_7003130
  have hstable : (prefixWord ++ tailWord_7003130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003130).length < 2 ^ (prefixWord ++ tailWord_7003130).sum := by decide
  have hdescent : baseEnd_7003130 < baseStart_7003130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003165 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_7003165 : Nat := 118140960795 + 7003165 * 2 ^ 59
def prefixEnd_7003165 : Nat := 4983230072969 + 3 ^ 40 * 7003165 * 2
def baseEnd_7003165 : Nat := 3595989747744197818430537

theorem tailTrace_7003165 : CollatzResearch.WordTrace tailWord_7003165 prefixEnd_7003165 3595989747744197818430537 := by
  unfold tailWord_7003165
  simp only [CollatzResearch.WordTrace]
  refine ⟨255426411673736725205074949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170284274449157816803383299 255426411673736725205074949)
  ·
    refine ⟨47892452188825635975951553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255426411673736725205074949 47892452188825635975951553)
    ·
      refine ⟨35919339141619226981963665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47892452188825635975951553 35919339141619226981963665)
      ·
        refine ⟨26939504356214420236472749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35919339141619226981963665 26939504356214420236472749)
        ·
          refine ⟨10102314133580407588677281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26939504356214420236472749 10102314133580407588677281)
          ·
            refine ⟨7576735600185305691507961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10102314133580407588677281 7576735600185305691507961)
            ·
              refine ⟨5682551700138979268630971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7576735600185305691507961 5682551700138979268630971)
              ·
                refine ⟨8523827550208468902946457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682551700138979268630971 8523827550208468902946457)
                ·
                  refine ⟨6392870662656351677209843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8523827550208468902946457 6392870662656351677209843)
                  ·
                    refine ⟨9589305993984527515814765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6392870662656351677209843 9589305993984527515814765)
                    ·
                      refine ⟨3595989747744197818430537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589305993984527515814765 3595989747744197818430537)
                      ·
                        rfl

theorem cell23_7003165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_7003165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003165 prefixEnd_7003165 := by exact prefixLift 7003165
  have htrace : WordTrace (prefixWord ++ tailWord_7003165) baseStart_7003165 baseEnd_7003165 := by
    simpa [prefixWord, tailWord_7003165, baseEnd_7003165] using wordTrace_append hprefix tailTrace_7003165
  have hstable : (prefixWord ++ tailWord_7003165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003165).length < 2 ^ (prefixWord ++ tailWord_7003165).sum := by decide
  have hdescent : baseEnd_7003165 < baseStart_7003165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003175 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_7003175 : Nat := 118140960795 + 7003175 * 2 ^ 59
def prefixEnd_7003175 : Nat := 4983230072969 + 3 ^ 40 * 7003175 * 2
def baseEnd_7003175 : Nat := 3595994882550742779305491

theorem tailTrace_7003175 : CollatzResearch.WordTrace tailWord_7003175 prefixEnd_7003175 3595994882550742779305491 := by
  unfold tailWord_7003175
  simp only [CollatzResearch.WordTrace]
  refine ⟨255426776403700496912938979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170284517602466997941959319 255426776403700496912938979)
  ·
    refine ⟨383140164605550745369408469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255426776403700496912938979 383140164605550745369408469)
    ·
      refine ⟨8979847607942595594595511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 383140164605550745369408469 8979847607942595594595511)
      ·
        refine ⟨13469771411913893391893267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8979847607942595594595511 13469771411913893391893267)
        ·
          refine ⟨20204657117870840087839901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13469771411913893391893267 20204657117870840087839901)
          ·
            refine ⟨7576746419201565032939963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20204657117870840087839901 7576746419201565032939963)
            ·
              refine ⟨11365119628802347549409945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7576746419201565032939963 11365119628802347549409945)
              ·
                refine ⟨8523839721601760662057459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11365119628802347549409945 8523839721601760662057459)
                ·
                  refine ⟨12785759582402640993086189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523839721601760662057459 12785759582402640993086189)
                  ·
                    refine ⟨4794659843400990372407321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12785759582402640993086189 4794659843400990372407321)
                    ·
                      refine ⟨3595994882550742779305491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794659843400990372407321 3595994882550742779305491)
                      ·
                        rfl

theorem cell23_7003175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_7003175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003175 prefixEnd_7003175 := by exact prefixLift 7003175
  have htrace : WordTrace (prefixWord ++ tailWord_7003175) baseStart_7003175 baseEnd_7003175 := by
    simpa [prefixWord, tailWord_7003175, baseEnd_7003175] using wordTrace_append hprefix tailTrace_7003175
  have hstable : (prefixWord ++ tailWord_7003175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003175).length < 2 ^ (prefixWord ++ tailWord_7003175).sum := by decide
  have hdescent : baseEnd_7003175 < baseStart_7003175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003187 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 3]
def baseStart_7003187 : Nat := 118140960795 + 7003187 * 2 ^ 59
def prefixEnd_7003187 : Nat := 4983230072969 + 3 ^ 40 * 7003187 * 2
def baseEnd_7003187 : Nat := 3596001044318596732355435

theorem tailTrace_7003187 : CollatzResearch.WordTrace tailWord_7003187 prefixEnd_7003187 3596001044318596732355435 := by
  unfold tailWord_7003187
  simp only [CollatzResearch.WordTrace]
  refine ⟨255427214079657022962375815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170284809386438015308250543 255427214079657022962375815)
  ·
    refine ⟨383140821119485534443563723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255427214079657022962375815 383140821119485534443563723)
    ·
      refine ⟨574711231679228301665345585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383140821119485534443563723 574711231679228301665345585)
      ·
        refine ⟨431033423759421226249009189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574711231679228301665345585 431033423759421226249009189)
        ·
          refine ⟨80818766954891479921689223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431033423759421226249009189 80818766954891479921689223)
          ·
            refine ⟨121228150432337219882533835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80818766954891479921689223 121228150432337219882533835)
            ·
              refine ⟨181842225648505829823800753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121228150432337219882533835 181842225648505829823800753)
              ·
                refine ⟨136381669236379372367850565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181842225648505829823800753 136381669236379372367850565)
                ·
                  refine ⟨25571562981821132318971981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136381669236379372367850565 25571562981821132318971981)
                  ·
                    refine ⟨9589336118182924619614493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25571562981821132318971981 9589336118182924619614493)
                    ·
                      refine ⟨3596001044318596732355435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589336118182924619614493 3596001044318596732355435)
                      ·
                        rfl

theorem cell23_7003187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_7003187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003187 prefixEnd_7003187 := by exact prefixLift 7003187
  have htrace : WordTrace (prefixWord ++ tailWord_7003187) baseStart_7003187 baseEnd_7003187 := by
    simpa [prefixWord, tailWord_7003187, baseEnd_7003187] using wordTrace_append hprefix tailTrace_7003187
  have hstable : (prefixWord ++ tailWord_7003187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003187).length < 2 ^ (prefixWord ++ tailWord_7003187).sum := by decide
  have hdescent : baseEnd_7003187 < baseStart_7003187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003188 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7003188 : Nat := 118140960795 + 7003188 * 2 ^ 59
def prefixEnd_7003188 : Nat := 4983230072969 + 3 ^ 40 * 7003188 * 2
def baseEnd_7003188 : Nat := 3596001557799251228442931

theorem tailTrace_7003188 : CollatzResearch.WordTrace tailWord_7003188 prefixEnd_7003188 3596001557799251228442931 := by
  unfold tailWord_7003188
  simp only [CollatzResearch.WordTrace]
  refine ⟨127713625276326700066581109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170284833701768933422108145 127713625276326700066581109)
  ·
    refine ⟨11973152369655628131241979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127713625276326700066581109 11973152369655628131241979)
    ·
      refine ⟨17959728554483442196862969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11973152369655628131241979 17959728554483442196862969)
      ·
        refine ⟨13469796415862581647647227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17959728554483442196862969 13469796415862581647647227)
        ·
          refine ⟨20204694623793872471470841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13469796415862581647647227 20204694623793872471470841)
          ·
            refine ⟨15153520967845404353603131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20204694623793872471470841 15153520967845404353603131)
            ·
              refine ⟨22730281451768106530404697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15153520967845404353603131 22730281451768106530404697)
              ·
                refine ⟨17047711088826079897803523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22730281451768106530404697 17047711088826079897803523)
                ·
                  refine ⟨25571566633239119846705285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17047711088826079897803523 25571566633239119846705285)
                  ·
                    refine ⟨4794668743732334971257241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25571566633239119846705285 4794668743732334971257241)
                    ·
                      refine ⟨3596001557799251228442931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794668743732334971257241 3596001557799251228442931)
                      ·
                        rfl

theorem cell23_7003188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7003188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003188 prefixEnd_7003188 := by exact prefixLift 7003188
  have htrace : WordTrace (prefixWord ++ tailWord_7003188) baseStart_7003188 baseEnd_7003188 := by
    simpa [prefixWord, tailWord_7003188, baseEnd_7003188] using wordTrace_append hprefix tailTrace_7003188
  have hstable : (prefixWord ++ tailWord_7003188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003188).length < 2 ^ (prefixWord ++ tailWord_7003188).sum := by decide
  have hdescent : baseEnd_7003188 < baseStart_7003188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003214 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_7003214 : Nat := 118140960795 + 7003214 * 2 ^ 59
def prefixEnd_7003214 : Nat := 4983230072969 + 3 ^ 40 * 7003214 * 2
def baseEnd_7003214 : Nat := 3596014908296268126717811

theorem tailTrace_7003214 : CollatzResearch.WordTrace tailWord_7003214 prefixEnd_7003214 3596014908296268126717811 := by
  unfold tailWord_7003214
  simp only [CollatzResearch.WordTrace]
  refine ⟨31928524856319900821701087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170285465900372804382405797 31928524856319900821701087)
  ·
    refine ⟨47892787284479851232551631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31928524856319900821701087 47892787284479851232551631)
    ·
      refine ⟨71839180926719776848827447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47892787284479851232551631 71839180926719776848827447)
      ·
        refine ⟨107758771390079665273241171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71839180926719776848827447 107758771390079665273241171)
        ·
          refine ⟨161638157085119497909861757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107758771390079665273241171 161638157085119497909861757)
          ·
            refine ⟨60614308906919811716198159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161638157085119497909861757 60614308906919811716198159)
            ·
              refine ⟨90921463360379717574297239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60614308906919811716198159 90921463360379717574297239)
              ·
                refine ⟨136382195040569576361445859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90921463360379717574297239 136382195040569576361445859)
                ·
                  refine ⟨204573292560854364542168789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136382195040569576361445859 204573292560854364542168789)
                  ·
                    refine ⟨4794686544395024168957081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 204573292560854364542168789 4794686544395024168957081)
                    ·
                      refine ⟨3596014908296268126717811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794686544395024168957081 3596014908296268126717811)
                      ·
                        rfl

theorem cell23_7003214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_7003214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003214 prefixEnd_7003214 := by exact prefixLift 7003214
  have htrace : WordTrace (prefixWord ++ tailWord_7003214) baseStart_7003214 baseEnd_7003214 := by
    simpa [prefixWord, tailWord_7003214, baseEnd_7003214] using wordTrace_append hprefix tailTrace_7003214
  have hstable : (prefixWord ++ tailWord_7003214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003214).length < 2 ^ (prefixWord ++ tailWord_7003214).sum := by decide
  have hdescent : baseEnd_7003214 < baseStart_7003214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003217 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_7003217 : Nat := 118140960795 + 7003217 * 2 ^ 59
def prefixEnd_7003217 : Nat := 4983230072969 + 3 ^ 40 * 7003217 * 2
def baseEnd_7003217 : Nat := 3596016448738231614980297

theorem tailTrace_7003217 : CollatzResearch.WordTrace tailWord_7003217 prefixEnd_7003217 3596016448738231614980297 := by
  unfold tailWord_7003217
  simp only [CollatzResearch.WordTrace]
  refine ⟨255428308269548338085967905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170285538846365558723978603 255428308269548338085967905)
  ·
    refine ⟨191571231202161253564475929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255428308269548338085967905 191571231202161253564475929)
    ·
      refine ⟨143678423401620940173356947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191571231202161253564475929 143678423401620940173356947)
      ·
        refine ⟨215517635102431410260035421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143678423401620940173356947 215517635102431410260035421)
        ·
          refine ⟨80819113163411778847513283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215517635102431410260035421 80819113163411778847513283)
          ·
            refine ⟨121228669745117668271269925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80819113163411778847513283 121228669745117668271269925)
            ·
              refine ⟨22730375577209562800863111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121228669745117668271269925 22730375577209562800863111)
              ·
                refine ⟨34095563365814344201294667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22730375577209562800863111 34095563365814344201294667)
                ·
                  refine ⟨51143345048721516301942001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34095563365814344201294667 51143345048721516301942001)
                  ·
                    refine ⟨38357508786541137226456501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51143345048721516301942001 38357508786541137226456501)
                    ·
                      refine ⟨3596016448738231614980297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38357508786541137226456501 3596016448738231614980297)
                      ·
                        rfl

theorem cell23_7003217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_7003217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003217 prefixEnd_7003217 := by exact prefixLift 7003217
  have htrace : WordTrace (prefixWord ++ tailWord_7003217) baseStart_7003217 baseEnd_7003217 := by
    simpa [prefixWord, tailWord_7003217, baseEnd_7003217] using wordTrace_append hprefix tailTrace_7003217
  have hstable : (prefixWord ++ tailWord_7003217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003217).length < 2 ^ (prefixWord ++ tailWord_7003217).sum := by decide
  have hdescent : baseEnd_7003217 < baseStart_7003217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003244 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 1, 6, 2]
def baseStart_7003244 : Nat := 118140960795 + 7003244 * 2 ^ 59
def prefixEnd_7003244 : Nat := 4983230072969 + 3 ^ 40 * 7003244 * 2
def baseEnd_7003244 : Nat := 3596030312715903009342673

theorem tailTrace_7003244 : CollatzResearch.WordTrace tailWord_7003244 prefixEnd_7003244 3596030312715903009342673 := by
  unfold tailWord_7003244
  simp only [CollatzResearch.WordTrace]
  refine ⟨127714646520225260848600393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170286195360300347798133857 127714646520225260848600393)
  ·
    refine ⟨95785984890168945636450295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127714646520225260848600393 95785984890168945636450295)
    ·
      refine ⟨143678977335253418454675443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95785984890168945636450295 143678977335253418454675443)
      ·
        refine ⟨215518466002880127682013165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143678977335253418454675443 215518466002880127682013165)
        ·
          refine ⟨80819424751080047880754937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215518466002880127682013165 80819424751080047880754937)
          ·
            refine ⟨60614568563310035910566203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80819424751080047880754937 60614568563310035910566203)
            ·
              refine ⟨90921852844965053865849305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60614568563310035910566203 90921852844965053865849305)
              ·
                refine ⟨68191389633723790399386979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90921852844965053865849305 68191389633723790399386979)
                ·
                  refine ⟨102287084450585685599080469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68191389633723790399386979 102287084450585685599080469)
                  ·
                    refine ⟨4794707083621204012456897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102287084450585685599080469 4794707083621204012456897)
                    ·
                      refine ⟨3596030312715903009342673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794707083621204012456897 3596030312715903009342673)
                      ·
                        rfl

theorem cell23_7003244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_7003244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003244 prefixEnd_7003244 := by exact prefixLift 7003244
  have htrace : WordTrace (prefixWord ++ tailWord_7003244) baseStart_7003244 baseEnd_7003244 := by
    simpa [prefixWord, tailWord_7003244, baseEnd_7003244] using wordTrace_append hprefix tailTrace_7003244
  have hstable : (prefixWord ++ tailWord_7003244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003244).length < 2 ^ (prefixWord ++ tailWord_7003244).sum := by decide
  have hdescent : baseEnd_7003244 < baseStart_7003244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003264 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 3]
def baseStart_7003264 : Nat := 118140960795 + 7003264 * 2 ^ 59
def prefixEnd_7003264 : Nat := 4983230072969 + 3 ^ 40 * 7003264 * 2
def baseEnd_7003264 : Nat := 3596040582328992931092581

theorem tailTrace_7003264 : CollatzResearch.WordTrace tailWord_7003264 prefixEnd_7003264 3596040582328992931092581 := by
  unfold tailWord_7003264
  simp only [CollatzResearch.WordTrace]
  refine ⟨127715011250189032556464423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170286681666918710075285897 127715011250189032556464423)
  ·
    refine ⟨191572516875283548834696635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127715011250189032556464423 191572516875283548834696635)
    ·
      refine ⟨287358775312925323252044953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191572516875283548834696635 287358775312925323252044953)
      ·
        refine ⟨215519081484693992439033715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287358775312925323252044953 215519081484693992439033715)
        ·
          refine ⟨323278622227040988658550573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215519081484693992439033715 323278622227040988658550573)
          ·
            refine ⟨121229483335140370746956465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323278622227040988658550573 121229483335140370746956465)
            ·
              refine ⟨90922112501355278060217349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121229483335140370746956465 90922112501355278060217349)
              ·
                refine ⟨17047896094004114636290753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90922112501355278060217349 17047896094004114636290753)
                ·
                  refine ⟨12785922070503085977218065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17047896094004114636290753 12785922070503085977218065)
                  ·
                    refine ⟨9589441552877314482913549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12785922070503085977218065 9589441552877314482913549)
                    ·
                      refine ⟨3596040582328992931092581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589441552877314482913549 3596040582328992931092581)
                      ·
                        rfl

theorem cell23_7003264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_7003264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003264 prefixEnd_7003264 := by exact prefixLift 7003264
  have htrace : WordTrace (prefixWord ++ tailWord_7003264) baseStart_7003264 baseEnd_7003264 := by
    simpa [prefixWord, tailWord_7003264, baseEnd_7003264] using wordTrace_append hprefix tailTrace_7003264
  have hstable : (prefixWord ++ tailWord_7003264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003264).length < 2 ^ (prefixWord ++ tailWord_7003264).sum := by decide
  have hdescent : baseEnd_7003264 < baseStart_7003264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003267 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 8]
def baseStart_7003267 : Nat := 118140960795 + 7003267 * 2 ^ 59
def prefixEnd_7003267 : Nat := 4983230072969 + 3 ^ 40 * 7003267 * 2
def baseEnd_7003267 : Nat := 399560235863439602150563

theorem tailTrace_7003267 : CollatzResearch.WordTrace tailWord_7003267 prefixEnd_7003267 399560235863439602150563 := by
  unfold tailWord_7003267
  simp only [CollatzResearch.WordTrace]
  refine ⟨255430131919367196625288055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170286754612911464416858703 255430131919367196625288055)
  ·
    refine ⟨383145197879050794937932083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255430131919367196625288055 383145197879050794937932083)
    ·
      refine ⟨574717796818576192406898125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383145197879050794937932083 574717796818576192406898125)
      ·
        refine ⟨215519173806966072152586797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574717796818576192406898125 215519173806966072152586797)
        ·
          refine ⟨80819690177612277057220049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215519173806966072152586797 80819690177612277057220049)
          ·
            refine ⟨60614767633209207792915037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80819690177612277057220049 60614767633209207792915037)
            ·
              refine ⟨22730537862453452922343139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60614767633209207792915037 22730537862453452922343139)
              ·
                refine ⟨34095806793680179383514709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22730537862453452922343139 34095806793680179383514709)
                ·
                  refine ⟨399560235863439602150563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34095806793680179383514709 399560235863439602150563)
                  ·
                    rfl

theorem cell23_7003267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 8].length) (baseStart_7003267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003267 prefixEnd_7003267 := by exact prefixLift 7003267
  have htrace : WordTrace (prefixWord ++ tailWord_7003267) baseStart_7003267 baseEnd_7003267 := by
    simpa [prefixWord, tailWord_7003267, baseEnd_7003267] using wordTrace_append hprefix tailTrace_7003267
  have hstable : (prefixWord ++ tailWord_7003267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003267).length < 2 ^ (prefixWord ++ tailWord_7003267).sum := by decide
  have hdescent : baseEnd_7003267 < baseStart_7003267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003321 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 4, 3, 2]
def baseStart_7003321 : Nat := 118140960795 + 7003321 * 2 ^ 59
def prefixEnd_7003321 : Nat := 4983230072969 + 3 ^ 40 * 7003321 * 2
def baseEnd_7003321 : Nat := 3596069850726299208079819

theorem tailTrace_7003321 : CollatzResearch.WordTrace tailWord_7003321 prefixEnd_7003321 3596069850726299208079819 := by
  unfold tailWord_7003321
  simp only [CollatzResearch.WordTrace]
  refine ⟨255432101461171563847753817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170288067640781042565169211 255432101461171563847753817)
  ·
    refine ⟨191574076095878672885815363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255432101461171563847753817 191574076095878672885815363)
    ·
      refine ⟨287361114143818009328723045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191574076095878672885815363 287361114143818009328723045)
      ·
        refine ⟨53880208901965876749135571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287361114143818009328723045 53880208901965876749135571)
        ·
          refine ⟨80820313352948815123703357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53880208901965876749135571 80820313352948815123703357)
          ·
            refine ⟨30307617507355805671388759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80820313352948815123703357 30307617507355805671388759)
            ·
              refine ⟨45461426261033708507083139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30307617507355805671388759 45461426261033708507083139)
              ·
                refine ⟨68192139391550562760624709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45461426261033708507083139 68192139391550562760624709)
                ·
                  refine ⟨12786026135915730517617133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68192139391550562760624709 12786026135915730517617133)
                  ·
                    refine ⟨4794759800968398944106425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12786026135915730517617133 4794759800968398944106425)
                    ·
                      refine ⟨3596069850726299208079819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794759800968398944106425 3596069850726299208079819)
                      ·
                        rfl

theorem cell23_7003321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_7003321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003321 prefixEnd_7003321 := by exact prefixLift 7003321
  have htrace : WordTrace (prefixWord ++ tailWord_7003321) baseStart_7003321 baseEnd_7003321 := by
    simpa [prefixWord, tailWord_7003321, baseEnd_7003321] using wordTrace_append hprefix tailTrace_7003321
  have hstable : (prefixWord ++ tailWord_7003321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003321).length < 2 ^ (prefixWord ++ tailWord_7003321).sum := by decide
  have hdescent : baseEnd_7003321 < baseStart_7003321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003337 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_7003337 : Nat := 118140960795 + 7003337 * 2 ^ 59
def prefixEnd_7003337 : Nat := 4983230072969 + 3 ^ 40 * 7003337 * 2
def baseEnd_7003337 : Nat := 3596078066416771145479745

theorem tailTrace_7003337 : CollatzResearch.WordTrace tailWord_7003337 prefixEnd_7003337 3596078066416771145479745 := by
  unfold tailWord_7003337
  simp only [CollatzResearch.WordTrace]
  refine ⟨255432685029113598580336265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170288456686075732386890843 255432685029113598580336265)
  ·
    refine ⟨191574513771835198935252199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255432685029113598580336265 191574513771835198935252199)
    ·
      refine ⟨287361770657752798402878299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191574513771835198935252199 287361770657752798402878299)
      ·
        refine ⟨431042655986629197604317449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287361770657752798402878299 431042655986629197604317449)
        ·
          refine ⟨323281991989971898203238087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431042655986629197604317449 323281991989971898203238087)
          ·
            refine ⟨484922987984957847304857131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323281991989971898203238087 484922987984957847304857131)
            ·
              refine ⟨727384481977436770957285697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484922987984957847304857131 727384481977436770957285697)
              ·
                refine ⟨545538361483077578217964273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727384481977436770957285697 545538361483077578217964273)
                ·
                  refine ⟨409153771112308183663473205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545538361483077578217964273 409153771112308183663473205)
                  ·
                    refine ⟨38358166041778892218450613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 409153771112308183663473205 38358166041778892218450613)
                    ·
                      refine ⟨3596078066416771145479745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38358166041778892218450613 3596078066416771145479745)
                      ·
                        rfl

theorem cell23_7003337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_7003337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003337 prefixEnd_7003337 := by exact prefixLift 7003337
  have htrace : WordTrace (prefixWord ++ tailWord_7003337) baseStart_7003337 baseEnd_7003337 := by
    simpa [prefixWord, tailWord_7003337, baseEnd_7003337] using wordTrace_append hprefix tailTrace_7003337
  have hstable : (prefixWord ++ tailWord_7003337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003337).length < 2 ^ (prefixWord ++ tailWord_7003337).sum := by decide
  have hdescent : baseEnd_7003337 < baseStart_7003337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003348 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_7003348 : Nat := 118140960795 + 7003348 * 2 ^ 59
def prefixEnd_7003348 : Nat := 4983230072969 + 3 ^ 40 * 7003348 * 2
def baseEnd_7003348 : Nat := 1198694571567990200814065

theorem tailTrace_7003348 : CollatzResearch.WordTrace tailWord_7003348 prefixEnd_7003348 1198694571567990200814065 := by
  unfold tailWord_7003348
  simp only [CollatzResearch.WordTrace]
  refine ⟨127716543116036873729493349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170288724154715831639324465 127716543116036873729493349)
  ·
    refine ⟨23946851834256913824280003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127716543116036873729493349 23946851834256913824280003)
    ·
      refine ⟨35920277751385370736420005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23946851834256913824280003 35920277751385370736420005)
      ·
        refine ⟨6735052078384757013078751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35920277751385370736420005 6735052078384757013078751)
        ·
          refine ⟨10102578117577135519618127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6735052078384757013078751 10102578117577135519618127)
          ·
            refine ⟨15153867176365703279427191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102578117577135519618127 15153867176365703279427191)
            ·
              refine ⟨22730800764548554919140787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15153867176365703279427191 22730800764548554919140787)
              ·
                refine ⟨34096201146822832378711181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22730800764548554919140787 34096201146822832378711181)
                ·
                  refine ⟨12786075430058562142016693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34096201146822832378711181 12786075430058562142016693)
                  ·
                    refine ⟨1198694571567990200814065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12786075430058562142016693 1198694571567990200814065)
                    ·
                      rfl

theorem cell23_7003348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_7003348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003348 prefixEnd_7003348 := by exact prefixLift 7003348
  have htrace : WordTrace (prefixWord ++ tailWord_7003348) baseStart_7003348 baseEnd_7003348 := by
    simpa [prefixWord, tailWord_7003348, baseEnd_7003348] using wordTrace_append hprefix tailTrace_7003348
  have hstable : (prefixWord ++ tailWord_7003348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003348).length < 2 ^ (prefixWord ++ tailWord_7003348).sum := by decide
  have hdescent : baseEnd_7003348 < baseStart_7003348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003351 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 4]
def baseStart_7003351 : Nat := 118140960795 + 7003351 * 2 ^ 59
def prefixEnd_7003351 : Nat := 4983230072969 + 3 ^ 40 * 7003351 * 2
def baseEnd_7003351 : Nat := 3596085255145934090704681

theorem tailTrace_7003351 : CollatzResearch.WordTrace tailWord_7003351 prefixEnd_7003351 3596085255145934090704681 := by
  unfold tailWord_7003351
  simp only [CollatzResearch.WordTrace]
  refine ⟨255433195651062878971345907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170288797100708585980897271 255433195651062878971345907)
  ·
    refine ⟨383149793476594318457018861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255433195651062878971345907 383149793476594318457018861)
    ·
      refine ⟨143681172553722869421382073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383149793476594318457018861 143681172553722869421382073)
      ·
        refine ⟨107760879415292152066036555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143681172553722869421382073 107760879415292152066036555)
        ·
          refine ⟨161641319122938228099054833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107760879415292152066036555 161641319122938228099054833)
          ·
            refine ⟨121230989342203671074291125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161641319122938228099054833 121230989342203671074291125)
            ·
              refine ⟨11365405250831594163214793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121230989342203671074291125 11365405250831594163214793)
              ·
                refine ⟨8524053938123695622411095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11365405250831594163214793 8524053938123695622411095)
                ·
                  refine ⟨12786080907185543433616643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524053938123695622411095 12786080907185543433616643)
                  ·
                    refine ⟨19179121360778315150424965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12786080907185543433616643 19179121360778315150424965)
                    ·
                      refine ⟨3596085255145934090704681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19179121360778315150424965 3596085255145934090704681)
                      ·
                        rfl

theorem cell23_7003351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_7003351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003351 prefixEnd_7003351 := by exact prefixLift 7003351
  have htrace : WordTrace (prefixWord ++ tailWord_7003351) baseStart_7003351 baseEnd_7003351 := by
    simpa [prefixWord, tailWord_7003351, baseEnd_7003351] using wordTrace_append hprefix tailTrace_7003351
  have hstable : (prefixWord ++ tailWord_7003351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003351).length < 2 ^ (prefixWord ++ tailWord_7003351).sum := by decide
  have hdescent : baseEnd_7003351 < baseStart_7003351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003364 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_7003364 : Nat := 118140960795 + 7003364 * 2 ^ 59
def prefixEnd_7003364 : Nat := 4983230072969 + 3 ^ 40 * 7003364 * 2
def baseEnd_7003364 : Nat := 3596091930394442539842121

theorem tailTrace_7003364 : CollatzResearch.WordTrace tailWord_7003364 prefixEnd_7003364 3596091930394442539842121 := by
  unfold tailWord_7003364
  simp only [CollatzResearch.WordTrace]
  refine ⟨127716834900007891095784573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170289113200010521461046097 127716834900007891095784573)
  ·
    refine ⟨47893813087502959160919215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127716834900007891095784573 47893813087502959160919215)
    ·
      refine ⟨71840719631254438741378823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47893813087502959160919215 71840719631254438741378823)
      ·
        refine ⟨107761079446881658112068235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71840719631254438741378823 107761079446881658112068235)
        ·
          refine ⟨161641619170322487168102353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107761079446881658112068235 161641619170322487168102353)
          ·
            refine ⟨121231214377741865376076765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161641619170322487168102353 121231214377741865376076765)
            ·
              refine ⟨45461705391653199516028787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121231214377741865376076765 45461705391653199516028787)
              ·
                refine ⟨68192558087479799274043181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45461705391653199516028787 68192558087479799274043181)
                ·
                  refine ⟨25572209282804924727766193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68192558087479799274043181 25572209282804924727766193)
                  ·
                    refine ⟨19179156962103693545824645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25572209282804924727766193 19179156962103693545824645)
                    ·
                      refine ⟨3596091930394442539842121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19179156962103693545824645 3596091930394442539842121)
                      ·
                        rfl

theorem cell23_7003364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_7003364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003364 prefixEnd_7003364 := by exact prefixLift 7003364
  have htrace : WordTrace (prefixWord ++ tailWord_7003364) baseStart_7003364 baseEnd_7003364 := by
    simpa [prefixWord, tailWord_7003364, baseEnd_7003364] using wordTrace_append hprefix tailTrace_7003364
  have hstable : (prefixWord ++ tailWord_7003364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003364).length < 2 ^ (prefixWord ++ tailWord_7003364).sum := by decide
  have hdescent : baseEnd_7003364 < baseStart_7003364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003368 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_7003368 : Nat := 118140960795 + 7003368 * 2 ^ 59
def prefixEnd_7003368 : Nat := 4983230072969 + 3 ^ 40 * 7003368 * 2
def baseEnd_7003368 : Nat := 3596093984317060524192103

theorem tailTrace_7003368 : CollatzResearch.WordTrace tailWord_7003368 prefixEnd_7003368 3596093984317060524192103 := by
  unfold tailWord_7003368
  simp only [CollatzResearch.WordTrace]
  refine ⟨127716907846000645437357379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170289210461334193916476505 127716907846000645437357379)
  ·
    refine ⟨191575361769000968156036069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127716907846000645437357379 191575361769000968156036069)
    ·
      refine ⟨35920380331687681529256763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191575361769000968156036069 35920380331687681529256763)
      ·
        refine ⟨53880570497531522293885145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35920380331687681529256763 53880570497531522293885145)
        ·
          refine ⟨40410427873148641720413859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53880570497531522293885145 40410427873148641720413859)
          ·
            refine ⟨60615641809722962580620789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40410427873148641720413859 60615641809722962580620789)
            ·
              refine ⟨5682716419661527741933199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60615641809722962580620789 5682716419661527741933199)
              ·
                refine ⟨8524074629492291612899799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682716419661527741933199 8524074629492291612899799)
                ·
                  refine ⟨12786111944238437419349699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524074629492291612899799 12786111944238437419349699)
                  ·
                    refine ⟨19179167916357656129024549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12786111944238437419349699 19179167916357656129024549)
                    ·
                      refine ⟨3596093984317060524192103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19179167916357656129024549 3596093984317060524192103)
                      ·
                        rfl

theorem cell23_7003368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_7003368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003368 prefixEnd_7003368 := by exact prefixLift 7003368
  have htrace : WordTrace (prefixWord ++ tailWord_7003368) baseStart_7003368 baseEnd_7003368 := by
    simpa [prefixWord, tailWord_7003368, baseEnd_7003368] using wordTrace_append hprefix tailTrace_7003368
  have hstable : (prefixWord ++ tailWord_7003368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003368).length < 2 ^ (prefixWord ++ tailWord_7003368).sum := by decide
  have hdescent : baseEnd_7003368 < baseStart_7003368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003371 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 5]
def baseStart_7003371 : Nat := 118140960795 + 7003371 * 2 ^ 59
def prefixEnd_7003371 : Nat := 4983230072969 + 3 ^ 40 * 7003371 * 2
def baseEnd_7003371 : Nat := 3596095524759024012454589

theorem tailTrace_7003371 : CollatzResearch.WordTrace tailWord_7003371 prefixEnd_7003371 3596095524759024012454589 := by
  unfold tailWord_7003371
  simp only [CollatzResearch.WordTrace]
  refine ⟨255433925110990422387073967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170289283407326948258049311 255433925110990422387073967)
  ·
    refine ⟨383150887666485633580610951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255433925110990422387073967 383150887666485633580610951)
    ·
      refine ⟨574726331499728450370916427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383150887666485633580610951 574726331499728450370916427)
      ·
        refine ⟨862089497249592675556374641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574726331499728450370916427 862089497249592675556374641)
        ·
          refine ⟨646567122937194506667280981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862089497249592675556374641 646567122937194506667280981)
          ·
            refine ⟨7576958471920248125007199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 646567122937194506667280981 7576958471920248125007199)
            ·
              refine ⟨11365437707880372187510799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7576958471920248125007199 11365437707880372187510799)
              ·
                refine ⟨17048156561820558281266199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11365437707880372187510799 17048156561820558281266199)
                ·
                  refine ⟨25572234842730837421899299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17048156561820558281266199 25572234842730837421899299)
                  ·
                    refine ⟨38358352264096256132848949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25572234842730837421899299 38358352264096256132848949)
                    ·
                      refine ⟨3596095524759024012454589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38358352264096256132848949 3596095524759024012454589)
                      ·
                        rfl

theorem cell23_7003371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 5].length) (baseStart_7003371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003371 prefixEnd_7003371 := by exact prefixLift 7003371
  have htrace : WordTrace (prefixWord ++ tailWord_7003371) baseStart_7003371 baseEnd_7003371 := by
    simpa [prefixWord, tailWord_7003371, baseEnd_7003371] using wordTrace_append hprefix tailTrace_7003371
  have hstable : (prefixWord ++ tailWord_7003371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003371).length < 2 ^ (prefixWord ++ tailWord_7003371).sum := by decide
  have hdescent : baseEnd_7003371 < baseStart_7003371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003385 : List Nat := [1, 2, 1, 3, 1, 1, 5, 4, 1, 2, 2]
def baseStart_7003385 : Nat := 118140960795 + 7003385 * 2 ^ 59
def prefixEnd_7003385 : Nat := 4983230072969 + 3 ^ 40 * 7003385 * 2
def baseEnd_7003385 : Nat := 3596102713488186957679525

theorem tailTrace_7003385 : CollatzResearch.WordTrace tailWord_7003385 prefixEnd_7003385 3596102713488186957679525 := by
  unfold tailWord_7003385
  simp only [CollatzResearch.WordTrace]
  refine ⟨255434435732939702778083609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170289623821959801852055739 255434435732939702778083609)
  ·
    refine ⟨191575826799704777083562707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255434435732939702778083609 191575826799704777083562707)
    ·
      refine ⟨287363740199557165625344061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191575826799704777083562707 287363740199557165625344061)
      ·
        refine ⟨107761402574833937109504023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287363740199557165625344061 107761402574833937109504023)
        ·
          refine ⟨161642103862250905664256035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107761402574833937109504023 161642103862250905664256035)
          ·
            refine ⟨242463155793376358496384053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161642103862250905664256035 242463155793376358496384053)
            ·
              refine ⟨22730920855629033609036005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242463155793376358496384053 22730920855629033609036005)
              ·
                refine ⟨4262047660430443801694251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22730920855629033609036005 4262047660430443801694251)
                ·
                  refine ⟨6393071490645665702541377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262047660430443801694251 6393071490645665702541377)
                  ·
                    refine ⟨4794803617984249276906033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6393071490645665702541377 4794803617984249276906033)
                    ·
                      refine ⟨3596102713488186957679525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794803617984249276906033 3596102713488186957679525)
                      ·
                        rfl

theorem cell23_7003385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_7003385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003385 prefixEnd_7003385 := by exact prefixLift 7003385
  have htrace : WordTrace (prefixWord ++ tailWord_7003385) baseStart_7003385 baseEnd_7003385 := by
    simpa [prefixWord, tailWord_7003385, baseEnd_7003385] using wordTrace_append hprefix tailTrace_7003385
  have hstable : (prefixWord ++ tailWord_7003385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003385).length < 2 ^ (prefixWord ++ tailWord_7003385).sum := by decide
  have hdescent : baseEnd_7003385 < baseStart_7003385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003401 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 3]
def baseStart_7003401 : Nat := 118140960795 + 7003401 * 2 ^ 59
def prefixEnd_7003401 : Nat := 4983230072969 + 3 ^ 40 * 7003401 * 2
def baseEnd_7003401 : Nat := 3596110929178658895079451

theorem tailTrace_7003401 : CollatzResearch.WordTrace tailWord_7003401 prefixEnd_7003401 3596110929178658895079451 := by
  unfold tailWord_7003401
  simp only [CollatzResearch.WordTrace]
  refine ⟨255435019300881737510666057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170290012867254491673777371 255435019300881737510666057)
  ·
    refine ⟨191576264475661303132999543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255435019300881737510666057 191576264475661303132999543)
    ·
      refine ⟨287364396713491954699499315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191576264475661303132999543 287364396713491954699499315)
      ·
        refine ⟨431046595070237932049248973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287364396713491954699499315 431046595070237932049248973)
        ·
          refine ⟨161642473151339224518468365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431046595070237932049248973 161642473151339224518468365)
          ·
            refine ⟨60615927431752209194425637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161642473151339224518468365 60615927431752209194425637)
            ·
              refine ⟨11365486393453539223954807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60615927431752209194425637 11365486393453539223954807)
              ·
                refine ⟨17048229590180308835932211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11365486393453539223954807 17048229590180308835932211)
                ·
                  refine ⟨25572344385270463253898317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17048229590180308835932211 25572344385270463253898317)
                  ·
                    refine ⟨9589629144476423720211869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25572344385270463253898317 9589629144476423720211869)
                    ·
                      refine ⟨3596110929178658895079451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589629144476423720211869 3596110929178658895079451)
                      ·
                        rfl

theorem cell23_7003401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_7003401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003401 prefixEnd_7003401 := by exact prefixLift 7003401
  have htrace : WordTrace (prefixWord ++ tailWord_7003401) baseStart_7003401 baseEnd_7003401 := by
    simpa [prefixWord, tailWord_7003401, baseEnd_7003401] using wordTrace_append hprefix tailTrace_7003401
  have hstable : (prefixWord ++ tailWord_7003401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003401).length < 2 ^ (prefixWord ++ tailWord_7003401).sum := by decide
  have hdescent : baseEnd_7003401 < baseStart_7003401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003422 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7003422 : Nat := 118140960795 + 7003422 * 2 ^ 59
def prefixEnd_7003422 : Nat := 4983230072969 + 3 ^ 40 * 7003422 * 2
def baseEnd_7003422 : Nat := 3596121712272403312916855

theorem tailTrace_7003422 : CollatzResearch.WordTrace tailWord_7003422 prefixEnd_7003422 3596121712272403312916855 := by
  unfold tailWord_7003422
  simp only [CollatzResearch.WordTrace]
  refine ⟨31929473154225707262147565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170290523489203772064787013 31929473154225707262147565)
  ·
    refine ⟨11973552432834640223305337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31929473154225707262147565 11973552432834640223305337)
    ·
      refine ⟨8980164324625980167479003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11973552432834640223305337 8980164324625980167479003)
      ·
        refine ⟨13470246486938970251218505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8980164324625980167479003 13470246486938970251218505)
        ·
          refine ⟨10102684865204227688413879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13470246486938970251218505 10102684865204227688413879)
          ·
            refine ⟨15154027297806341532620819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102684865204227688413879 15154027297806341532620819)
            ·
              refine ⟨22731040946709512298931229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15154027297806341532620819 22731040946709512298931229)
              ·
                refine ⟨8524140355016067112099211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22731040946709512298931229 8524140355016067112099211)
                ·
                  refine ⟨12786210532524100668148817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524140355016067112099211 12786210532524100668148817)
                  ·
                    refine ⟨9589657899393075501111613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12786210532524100668148817 9589657899393075501111613)
                    ·
                      refine ⟨3596121712272403312916855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589657899393075501111613 3596121712272403312916855)
                      ·
                        rfl

theorem cell23_7003422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7003422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003422 prefixEnd_7003422 := by exact prefixLift 7003422
  have htrace : WordTrace (prefixWord ++ tailWord_7003422) baseStart_7003422 baseEnd_7003422 := by
    simpa [prefixWord, tailWord_7003422, baseEnd_7003422] using wordTrace_append hprefix tailTrace_7003422
  have hstable : (prefixWord ++ tailWord_7003422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003422).length < 2 ^ (prefixWord ++ tailWord_7003422).sum := by decide
  have hdescent : baseEnd_7003422 < baseStart_7003422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003528 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 2, 5]
def baseStart_7003528 : Nat := 118140960795 + 7003528 * 2 ^ 59
def prefixEnd_7003528 : Nat := 4983230072969 + 3 ^ 40 * 7003528 * 2
def baseEnd_7003528 : Nat := 1198725380407259966063789

theorem tailTrace_7003528 : CollatzResearch.WordTrace tailWord_7003528 prefixEnd_7003528 1198725380407259966063789 := by
  unfold tailWord_7003528
  simp only [CollatzResearch.WordTrace]
  refine ⟨127719825685710819100269619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170293100914281092133692825 127719825685710819100269619)
  ·
    refine ⟨191579738528566228650404429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127719825685710819100269619 191579738528566228650404429)
    ·
      refine ⟨71842401948212335743901661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191579738528566228650404429 71842401948212335743901661)
      ·
        refine ⟨26940900730579625903963123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71842401948212335743901661 26940900730579625903963123)
        ·
          refine ⟨40411351095869438855944685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26940900730579625903963123 40411351095869438855944685)
          ·
            refine ⟨15154256660951039570979257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40411351095869438855944685 15154256660951039570979257)
            ·
              refine ⟨11365692495713279678234443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15154256660951039570979257 11365692495713279678234443)
              ·
                refine ⟨17048538743569919517351665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11365692495713279678234443 17048538743569919517351665)
                ·
                  refine ⟨12786404057677439638013749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17048538743569919517351665 12786404057677439638013749)
                  ·
                    refine ⟨1198725380407259966063789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12786404057677439638013749 1198725380407259966063789)
                    ·
                      rfl

theorem cell23_7003528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_7003528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003528 prefixEnd_7003528 := by exact prefixLift 7003528
  have htrace : WordTrace (prefixWord ++ tailWord_7003528) baseStart_7003528 baseEnd_7003528 := by
    simpa [prefixWord, tailWord_7003528, baseEnd_7003528] using wordTrace_append hprefix tailTrace_7003528
  have hstable : (prefixWord ++ tailWord_7003528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003528).length < 2 ^ (prefixWord ++ tailWord_7003528).sum := by decide
  have hdescent : baseEnd_7003528 < baseStart_7003528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003565 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7003565 : Nat := 118140960795 + 7003565 * 2 ^ 59
def prefixEnd_7003565 : Nat := 4983230072969 + 3 ^ 40 * 7003565 * 2
def baseEnd_7003565 : Nat := 3596195140005996253428697

theorem tailTrace_7003565 : CollatzResearch.WordTrace tailWord_7003565 prefixEnd_7003565 3596195140005996253428697 := by
  unfold tailWord_7003565
  simp only [CollatzResearch.WordTrace]
  refine ⟨255441000872287593519636149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170294000581525062346424099 255441000872287593519636149)
  ·
    refine ⟨23947593831776961892465889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255441000872287593519636149 23947593831776961892465889)
    ·
      refine ⟨17960695373832721419349417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23947593831776961892465889 17960695373832721419349417)
      ·
        refine ⟨13470521530374541064512063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17960695373832721419349417 13470521530374541064512063)
        ·
          refine ⟨20205782295561811596768095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13470521530374541064512063 20205782295561811596768095)
          ·
            refine ⟨30308673443342717395152143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20205782295561811596768095 30308673443342717395152143)
            ·
              refine ⟨45463010165014076092728215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30308673443342717395152143 45463010165014076092728215)
              ·
                refine ⟨68194515247521114139092323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45463010165014076092728215 68194515247521114139092323)
                ·
                  refine ⟨102291772871281671208638485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68194515247521114139092323 102291772871281671208638485)
                  ·
                    refine ⟨4794926853341328337904929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102291772871281671208638485 4794926853341328337904929)
                    ·
                      refine ⟨3596195140005996253428697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4794926853341328337904929 3596195140005996253428697)
                      ·
                        rfl

theorem cell23_7003565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7003565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003565 prefixEnd_7003565 := by exact prefixLift 7003565
  have htrace : WordTrace (prefixWord ++ tailWord_7003565) baseStart_7003565 baseEnd_7003565 := by
    simpa [prefixWord, tailWord_7003565, baseEnd_7003565] using wordTrace_append hprefix tailTrace_7003565
  have hstable : (prefixWord ++ tailWord_7003565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003565).length < 2 ^ (prefixWord ++ tailWord_7003565).sum := by decide
  have hdescent : baseEnd_7003565 < baseStart_7003565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003615 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 3]
def baseStart_7003615 : Nat := 118140960795 + 7003615 * 2 ^ 59
def prefixEnd_7003615 : Nat := 4983230072969 + 3 ^ 40 * 7003615 * 2
def baseEnd_7003615 : Nat := 3596220814038721057803467

theorem tailTrace_7003615 : CollatzResearch.WordTrace tailWord_7003615 prefixEnd_7003615 3596220814038721057803467 := by
  unfold tailWord_7003615
  simp only [CollatzResearch.WordTrace]
  refine ⟨255442824522106452058956299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170295216348070968039304199 255442824522106452058956299)
  ·
    refine ⟨383164236783159678088434449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255442824522106452058956299 383164236783159678088434449)
    ·
      refine ⟨287373177587369758566325837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383164236783159678088434449 287373177587369758566325837)
      ·
        refine ⟨107764941595263659462372189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287373177587369758566325837 107764941595263659462372189)
        ·
          refine ⟨40411853098223872298389571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107764941595263659462372189 40411853098223872298389571)
          ·
            refine ⟨60617779647335808447584357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40411853098223872298389571 60617779647335808447584357)
            ·
              refine ⟨11365833683875464083922067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60617779647335808447584357 11365833683875464083922067)
              ·
                refine ⟨17048750525813196125883101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11365833683875464083922067 17048750525813196125883101)
                ·
                  refine ⟨6393281447179948547206163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17048750525813196125883101 6393281447179948547206163)
                  ·
                    refine ⟨9589922170769922820809245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6393281447179948547206163 9589922170769922820809245)
                    ·
                      refine ⟨3596220814038721057803467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9589922170769922820809245 3596220814038721057803467)
                      ·
                        rfl

theorem cell23_7003615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_7003615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003615 prefixEnd_7003615 := by exact prefixLift 7003615
  have htrace : WordTrace (prefixWord ++ tailWord_7003615) baseStart_7003615 baseEnd_7003615 := by
    simpa [prefixWord, tailWord_7003615, baseEnd_7003615] using wordTrace_append hprefix tailTrace_7003615
  have hstable : (prefixWord ++ tailWord_7003615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003615).length < 2 ^ (prefixWord ++ tailWord_7003615).sum := by decide
  have hdescent : baseEnd_7003615 < baseStart_7003615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003641 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_7003641 : Nat := 118140960795 + 7003641 * 2 ^ 59
def prefixEnd_7003641 : Nat := 4983230072969 + 3 ^ 40 * 7003641 * 2
def baseEnd_7003641 : Nat := 3596234164535737956078347

theorem tailTrace_7003641 : CollatzResearch.WordTrace tailWord_7003641 prefixEnd_7003641 3596234164535737956078347 := by
  unfold tailWord_7003641
  simp only [CollatzResearch.WordTrace]
  refine ⟨255443772820012258499402777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170295848546674838999601851 255443772820012258499402777)
  ·
    refine ⟨191582829615009193874552083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255443772820012258499402777 191582829615009193874552083)
    ·
      refine ⟨287374244422513790811828125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191582829615009193874552083 287374244422513790811828125)
      ·
        refine ⟨107765341658442671554435547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287374244422513790811828125 107765341658442671554435547)
        ·
          refine ⟨161648012487664007331653321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107765341658442671554435547 161648012487664007331653321)
          ·
            refine ⟨121236009365748005498739991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161648012487664007331653321 121236009365748005498739991)
            ·
              refine ⟨181854014048622008248109987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121236009365748005498739991 181854014048622008248109987)
              ·
                refine ⟨272781021072933012372164981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181854014048622008248109987 272781021072933012372164981)
                ·
                  refine ⟨25573220725587469909890467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272781021072933012372164981 25573220725587469909890467)
                  ·
                    refine ⟨38359831088381204864835701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25573220725587469909890467 38359831088381204864835701)
                    ·
                      refine ⟨3596234164535737956078347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38359831088381204864835701 3596234164535737956078347)
                      ·
                        rfl

theorem cell23_7003641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_7003641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003641 prefixEnd_7003641 := by exact prefixLift 7003641
  have htrace : WordTrace (prefixWord ++ tailWord_7003641) baseStart_7003641 baseEnd_7003641 := by
    simpa [prefixWord, tailWord_7003641, baseEnd_7003641] using wordTrace_append hprefix tailTrace_7003641
  have hstable : (prefixWord ++ tailWord_7003641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003641).length < 2 ^ (prefixWord ++ tailWord_7003641).sum := by decide
  have hdescent : baseEnd_7003641 < baseStart_7003641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003655 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_7003655 : Nat := 118140960795 + 7003655 * 2 ^ 59
def prefixEnd_7003655 : Nat := 4983230072969 + 3 ^ 40 * 7003655 * 2
def baseEnd_7003655 : Nat := 3596241353264900901303283

theorem tailTrace_7003655 : CollatzResearch.WordTrace tailWord_7003655 prefixEnd_7003655 3596241353264900901303283 := by
  unfold tailWord_7003655
  simp only [CollatzResearch.WordTrace]
  refine ⟨255444283441961538890412419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170296188961307692593608279 255444283441961538890412419)
  ·
    refine ⟨383166425162942308335618629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255444283441961538890412419 383166425162942308335618629)
    ·
      refine ⟨71843704718051682812928493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383166425162942308335618629 71843704718051682812928493)
      ·
        refine ⟨26941389269269381054848185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71843704718051682812928493 26941389269269381054848185)
        ·
          refine ⟨20206041951952035791136139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26941389269269381054848185 20206041951952035791136139)
          ·
            refine ⟨30309062927928053686704209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20206041951952035791136139 30309062927928053686704209)
            ·
              refine ⟨22731797195946040265028157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30309062927928053686704209 22731797195946040265028157)
              ·
                refine ⟨8524423948479765099385559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22731797195946040265028157 8524423948479765099385559)
                ·
                  refine ⟨12786635922719647649078339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524423948479765099385559 12786635922719647649078339)
                  ·
                    refine ⟨19179953884079471473617509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12786635922719647649078339 19179953884079471473617509)
                    ·
                      refine ⟨3596241353264900901303283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19179953884079471473617509 3596241353264900901303283)
                      ·
                        rfl

theorem cell23_7003655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_7003655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003655 prefixEnd_7003655 := by exact prefixLift 7003655
  have htrace : WordTrace (prefixWord ++ tailWord_7003655) baseStart_7003655 baseEnd_7003655 := by
    simpa [prefixWord, tailWord_7003655, baseEnd_7003655] using wordTrace_append hprefix tailTrace_7003655
  have hstable : (prefixWord ++ tailWord_7003655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003655).length < 2 ^ (prefixWord ++ tailWord_7003655).sum := by decide
  have hdescent : baseEnd_7003655 < baseStart_7003655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003658 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_7003658 : Nat := 118140960795 + 7003658 * 2 ^ 59
def prefixEnd_7003658 : Nat := 4983230072969 + 3 ^ 40 * 7003658 * 2
def baseEnd_7003658 : Nat := 3596242893706864389565769

theorem tailTrace_7003658 : CollatzResearch.WordTrace tailWord_7003658 prefixEnd_7003658 3596242893706864389565769 := by
  unfold tailWord_7003658
  simp only [CollatzResearch.WordTrace]
  refine ⟨63861098215237667600692907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170296261907300446935181085 63861098215237667600692907)
  ·
    refine ⟨95791647322856501401039361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63861098215237667600692907 95791647322856501401039361)
    ·
      refine ⟨71843735492142376050779521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95791647322856501401039361 71843735492142376050779521)
      ·
        refine ⟨53882801619106782038084641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71843735492142376050779521 53882801619106782038084641)
        ·
          refine ⟨40412101214330086528563481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53882801619106782038084641 40412101214330086528563481)
          ·
            refine ⟨30309075910747564896422611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40412101214330086528563481 30309075910747564896422611)
            ·
              refine ⟨45463613866121347344633917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30309075910747564896422611 45463613866121347344633917)
              ·
                refine ⟨17048855199795505254237719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45463613866121347344633917 17048855199795505254237719)
                ·
                  refine ⟨25573282799693257881356579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17048855199795505254237719 25573282799693257881356579)
                  ·
                    refine ⟨38359924199539886822034869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25573282799693257881356579 38359924199539886822034869)
                    ·
                      refine ⟨3596242893706864389565769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38359924199539886822034869 3596242893706864389565769)
                      ·
                        rfl

theorem cell23_7003658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_7003658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003658 prefixEnd_7003658 := by exact prefixLift 7003658
  have htrace : WordTrace (prefixWord ++ tailWord_7003658) baseStart_7003658 baseEnd_7003658 := by
    simpa [prefixWord, tailWord_7003658, baseEnd_7003658] using wordTrace_append hprefix tailTrace_7003658
  have hstable : (prefixWord ++ tailWord_7003658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003658).length < 2 ^ (prefixWord ++ tailWord_7003658).sum := by decide
  have hdescent : baseEnd_7003658 < baseStart_7003658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003682 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_7003682 : Nat := 118140960795 + 7003682 * 2 ^ 59
def prefixEnd_7003682 : Nat := 4983230072969 + 3 ^ 40 * 7003682 * 2
def baseEnd_7003682 : Nat := 1198751739080857431888553

theorem tailTrace_7003682 : CollatzResearch.WordTrace tailWord_7003682 prefixEnd_7003682 1198751739080857431888553 := by
  unfold tailWord_7003682
  simp only [CollatzResearch.WordTrace]
  refine ⟨63861317053215930625411325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170296845475242481667763533 63861317053215930625411325)
  ·
    refine ⟨23947993894955973984529247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63861317053215930625411325 23947993894955973984529247)
    ·
      refine ⟨35921990842433960976793871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23947993894955973984529247 35921990842433960976793871)
      ·
        refine ⟨53882986263650941465190807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35921990842433960976793871 53882986263650941465190807)
        ·
          refine ⟨80824479395476412197786211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53882986263650941465190807 80824479395476412197786211)
          ·
            refine ⟨121236719093214618296679317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80824479395476412197786211 121236719093214618296679317)
            ·
              refine ⟨5682971207494435232656843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121236719093214618296679317 5682971207494435232656843)
              ·
                refine ⟨8524456811241652848985265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682971207494435232656843 8524456811241652848985265)
                ·
                  refine ⟨6393342608431239636738949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8524456811241652848985265 6393342608431239636738949)
                  ·
                    refine ⟨1198751739080857431888553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6393342608431239636738949 1198751739080857431888553)
                    ·
                      rfl

theorem cell23_7003682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_7003682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003682 prefixEnd_7003682 := by exact prefixLift 7003682
  have htrace : WordTrace (prefixWord ++ tailWord_7003682) baseStart_7003682 baseEnd_7003682 := by
    simpa [prefixWord, tailWord_7003682, baseEnd_7003682] using wordTrace_append hprefix tailTrace_7003682
  have hstable : (prefixWord ++ tailWord_7003682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003682).length < 2 ^ (prefixWord ++ tailWord_7003682).sum := by decide
  have hdescent : baseEnd_7003682 < baseStart_7003682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003702 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_7003702 : Nat := 118140960795 + 7003702 * 2 ^ 59
def prefixEnd_7003702 : Nat := 4983230072969 + 3 ^ 40 * 7003702 * 2
def baseEnd_7003702 : Nat := 3596265486855662217415567

theorem tailTrace_7003702 : CollatzResearch.WordTrace tailWord_7003702 prefixEnd_7003702 3596265486855662217415567 := by
  unfold tailWord_7003702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15965374854549454119835835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170297331781860843944915573 15965374854549454119835835)
  ·
    refine ⟨23948062281824181179753753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15965374854549454119835835 23948062281824181179753753)
    ·
      refine ⟨17961046711368135884815315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23948062281824181179753753 17961046711368135884815315)
      ·
        refine ⟨26941570067052203827222973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17961046711368135884815315 26941570067052203827222973)
        ·
          refine ⟨10103088775144576435208615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26941570067052203827222973 10103088775144576435208615)
          ·
            refine ⟨15154633162716864652812923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10103088775144576435208615 15154633162716864652812923)
            ·
              refine ⟨22731949744075296979219385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15154633162716864652812923 22731949744075296979219385)
              ·
                refine ⟨17048962308056472734414539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22731949744075296979219385 17048962308056472734414539)
                ·
                  refine ⟨25573443462084709101621809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17048962308056472734414539 25573443462084709101621809)
                  ·
                    refine ⟨19180082596563531826216357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25573443462084709101621809 19180082596563531826216357)
                    ·
                      refine ⟨3596265486855662217415567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19180082596563531826216357 3596265486855662217415567)
                      ·
                        rfl

theorem cell23_7003702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_7003702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003702 prefixEnd_7003702 := by exact prefixLift 7003702
  have htrace : WordTrace (prefixWord ++ tailWord_7003702) baseStart_7003702 baseEnd_7003702 := by
    simpa [prefixWord, tailWord_7003702, baseEnd_7003702] using wordTrace_append hprefix tailTrace_7003702
  have hstable : (prefixWord ++ tailWord_7003702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003702).length < 2 ^ (prefixWord ++ tailWord_7003702).sum := by decide
  have hdescent : baseEnd_7003702 < baseStart_7003702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003705 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 3]
def baseStart_7003705 : Nat := 118140960795 + 7003705 * 2 ^ 59
def prefixEnd_7003705 : Nat := 4983230072969 + 3 ^ 40 * 7003705 * 2
def baseEnd_7003705 : Nat := 3596267027297625705678053

theorem tailTrace_7003705 : CollatzResearch.WordTrace tailWord_7003705 prefixEnd_7003705 3596267027297625705678053 := by
  unfold tailWord_7003705
  simp only [CollatzResearch.WordTrace]
  refine ⟨255446107091780397429732569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170297404727853598286488379 255446107091780397429732569)
  ·
    refine ⟨191584580318835298072299427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255446107091780397429732569 191584580318835298072299427)
    ·
      refine ⟨287376870478252947108449141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191584580318835298072299427 287376870478252947108449141)
      ·
        refine ⟨26941581607336213791417107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 287376870478252947108449141 26941581607336213791417107)
        ·
          refine ⟨40412372411004320687125661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26941581607336213791417107 40412372411004320687125661)
          ·
            refine ⟨15154639654126620257672123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40412372411004320687125661 15154639654126620257672123)
            ·
              refine ⟨22731959481189930386508185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15154639654126620257672123 22731959481189930386508185)
              ·
                refine ⟨17048969610892447789881139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22731959481189930386508185 17048969610892447789881139)
                ·
                  refine ⟨25573454416338671684821709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17048969610892447789881139 25573454416338671684821709)
                  ·
                    refine ⟨9590045406127001881808141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25573454416338671684821709 9590045406127001881808141)
                    ·
                      refine ⟨3596267027297625705678053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9590045406127001881808141 3596267027297625705678053)
                      ·
                        rfl

theorem cell23_7003705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_7003705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003705 prefixEnd_7003705 := by exact prefixLift 7003705
  have htrace : WordTrace (prefixWord ++ tailWord_7003705) baseStart_7003705 baseEnd_7003705 := by
    simpa [prefixWord, tailWord_7003705, baseEnd_7003705] using wordTrace_append hprefix tailTrace_7003705
  have hstable : (prefixWord ++ tailWord_7003705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003705).length < 2 ^ (prefixWord ++ tailWord_7003705).sum := by decide
  have hdescent : baseEnd_7003705 < baseStart_7003705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003709 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_7003709 : Nat := 118140960795 + 7003709 * 2 ^ 59
def prefixEnd_7003709 : Nat := 4983230072969 + 3 ^ 40 * 7003709 * 2
def baseEnd_7003709 : Nat := 3596269081220243690028035

theorem tailTrace_7003709 : CollatzResearch.WordTrace tailWord_7003709 prefixEnd_7003709 3596269081220243690028035 := by
  unfold tailWord_7003709
  simp only [CollatzResearch.WordTrace]
  refine ⟨255446252983765906112878181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170297501989177270741918787 255446252983765906112878181)
  ·
    refine ⟨47896172434456107396164659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255446252983765906112878181 47896172434456107396164659)
    ·
      refine ⟨71844258651684161094246989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47896172434456107396164659 71844258651684161094246989)
      ·
        refine ⟨26941596994381560410342621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71844258651684161094246989 26941596994381560410342621)
        ·
          refine ⟨10103098872893085153878483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26941596994381560410342621 10103098872893085153878483)
          ·
            refine ⟨15154648309339627730817725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10103098872893085153878483 15154648309339627730817725)
            ·
              refine ⟨5682993116002360399056647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15154648309339627730817725 5682993116002360399056647)
              ·
                refine ⟨8524489674003540598584971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682993116002360399056647 8524489674003540598584971)
                ·
                  refine ⟨12786734511005310897877457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524489674003540598584971 12786734511005310897877457)
                  ·
                    refine ⟨9590050883253983173408093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12786734511005310897877457 9590050883253983173408093)
                    ·
                      refine ⟨3596269081220243690028035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9590050883253983173408093 3596269081220243690028035)
                      ·
                        rfl

theorem cell23_7003709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_7003709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003709 prefixEnd_7003709 := by exact prefixLift 7003709
  have htrace : WordTrace (prefixWord ++ tailWord_7003709) baseStart_7003709 baseEnd_7003709 := by
    simpa [prefixWord, tailWord_7003709, baseEnd_7003709] using wordTrace_append hprefix tailTrace_7003709
  have hstable : (prefixWord ++ tailWord_7003709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003709).length < 2 ^ (prefixWord ++ tailWord_7003709).sum := by decide
  have hdescent : baseEnd_7003709 < baseStart_7003709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003721 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 3, 8]
def baseStart_7003721 : Nat := 118140960795 + 7003721 * 2 ^ 59
def prefixEnd_7003721 : Nat := 4983230072969 + 3 ^ 40 * 7003721 * 2
def baseEnd_7003721 : Nat := 1198758414329365881025993

theorem tailTrace_7003721 : CollatzResearch.WordTrace tailWord_7003721 prefixEnd_7003721 1198758414329365881025993 := by
  unfold tailWord_7003721
  simp only [CollatzResearch.WordTrace]
  refine ⟨255446690659722432162315017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170297793773148288108210011 255446690659722432162315017)
  ·
    refine ⟨191585017994791824121736263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255446690659722432162315017 191585017994791824121736263)
    ·
      refine ⟨287377526992187736182604395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191585017994791824121736263 287377526992187736182604395)
      ·
        refine ⟨431066290488281604273906593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287377526992187736182604395 431066290488281604273906593)
        ·
          refine ⟨323299717866211203205429945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431066290488281604273906593 323299717866211203205429945)
          ·
            refine ⟨242474788399658402404072459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323299717866211203205429945 242474788399658402404072459)
            ·
              refine ⟨363712182599487603606108689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242474788399658402404072459 363712182599487603606108689)
              ·
                refine ⟨272784136949615702704581517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363712182599487603606108689 272784136949615702704581517)
                ·
                  refine ⟨102294051356105888514218069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272784136949615702704581517 102294051356105888514218069)
                  ·
                    refine ⟨1198758414329365881025993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102294051356105888514218069 1198758414329365881025993)
                    ·
                      rfl

theorem cell23_7003721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_7003721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003721 prefixEnd_7003721 := by exact prefixLift 7003721
  have htrace : WordTrace (prefixWord ++ tailWord_7003721) baseStart_7003721 baseEnd_7003721 := by
    simpa [prefixWord, tailWord_7003721, baseEnd_7003721] using wordTrace_append hprefix tailTrace_7003721
  have hstable : (prefixWord ++ tailWord_7003721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003721).length < 2 ^ (prefixWord ++ tailWord_7003721).sum := by decide
  have hdescent : baseEnd_7003721 < baseStart_7003721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003722 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_7003722 : Nat := 118140960795 + 7003722 * 2 ^ 59
def prefixEnd_7003722 : Nat := 4983230072969 + 3 ^ 40 * 7003722 * 2
def baseEnd_7003722 : Nat := 3596275756468752139165475

theorem tailTrace_7003722 : CollatzResearch.WordTrace tailWord_7003722 prefixEnd_7003722 3596275756468752139165475 := by
  unfold tailWord_7003722
  simp only [CollatzResearch.WordTrace]
  refine ⟨63861681783179702333275355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170297818088479206222067613 63861681783179702333275355)
  ·
    refine ⟨95792522674769553499913033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63861681783179702333275355 95792522674769553499913033)
    ·
      refine ⟨71844392006077165124934775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95792522674769553499913033 71844392006077165124934775)
      ·
        refine ⟨107766588009115747687402163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71844392006077165124934775 107766588009115747687402163)
        ·
          refine ⟨161649882013673621531103245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107766588009115747687402163 161649882013673621531103245)
          ·
            refine ⟨60618705755127608074163717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161649882013673621531103245 60618705755127608074163717)
            ·
              refine ⟨11366007329086426513905697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60618705755127608074163717 11366007329086426513905697)
              ·
                refine ⟨8524505496814819885429273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11366007329086426513905697 8524505496814819885429273)
                ·
                  refine ⟨6393379122611114914071955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8524505496814819885429273 6393379122611114914071955)
                  ·
                    refine ⟨9590068683916672371107933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6393379122611114914071955 9590068683916672371107933)
                    ·
                      refine ⟨3596275756468752139165475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9590068683916672371107933 3596275756468752139165475)
                      ·
                        rfl

theorem cell23_7003722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_7003722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003722 prefixEnd_7003722 := by exact prefixLift 7003722
  have htrace : WordTrace (prefixWord ++ tailWord_7003722) baseStart_7003722 baseEnd_7003722 := by
    simpa [prefixWord, tailWord_7003722, baseEnd_7003722] using wordTrace_append hprefix tailTrace_7003722
  have hstable : (prefixWord ++ tailWord_7003722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003722).length < 2 ^ (prefixWord ++ tailWord_7003722).sum := by decide
  have hdescent : baseEnd_7003722 < baseStart_7003722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003762 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_7003762 : Nat := 118140960795 + 7003762 * 2 ^ 59
def prefixEnd_7003762 : Nat := 4983230072969 + 3 ^ 40 * 7003762 * 2
def baseEnd_7003762 : Nat := 3596296295694931982665291

theorem tailTrace_7003762 : CollatzResearch.WordTrace tailWord_7003762 prefixEnd_7003762 3596296295694931982665291 := by
  unfold tailWord_7003762
  simp only [CollatzResearch.WordTrace]
  refine ⟨63862046513143474041139385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170298790701715930776371693 63862046513143474041139385)
  ·
    refine ⟨47896534884857605530854539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63862046513143474041139385 47896534884857605530854539)
    ·
      refine ⟨71844802327286408296281809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47896534884857605530854539 71844802327286408296281809)
      ·
        refine ⟨53883601745464806222211357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71844802327286408296281809 53883601745464806222211357)
        ·
          refine ⟨20206350654549302333329259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53883601745464806222211357 20206350654549302333329259)
          ·
            refine ⟨30309525981823953499993889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20206350654549302333329259 30309525981823953499993889)
            ·
              refine ⟨22732144486367965124995417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30309525981823953499993889 22732144486367965124995417)
              ·
                refine ⟨17049108364775973843746563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22732144486367965124995417 17049108364775973843746563)
                ·
                  refine ⟨25573662547163960765619845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17049108364775973843746563 25573662547163960765619845)
                  ·
                    refine ⟨4795061727593242643553721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25573662547163960765619845 4795061727593242643553721)
                    ·
                      refine ⟨3596296295694931982665291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795061727593242643553721 3596296295694931982665291)
                      ·
                        rfl

theorem cell23_7003762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_7003762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003762 prefixEnd_7003762 := by exact prefixLift 7003762
  have htrace : WordTrace (prefixWord ++ tailWord_7003762) baseStart_7003762 baseEnd_7003762 := by
    simpa [prefixWord, tailWord_7003762, baseEnd_7003762] using wordTrace_append hprefix tailTrace_7003762
  have hstable : (prefixWord ++ tailWord_7003762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003762).length < 2 ^ (prefixWord ++ tailWord_7003762).sum := by decide
  have hdescent : baseEnd_7003762 < baseStart_7003762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003766 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_7003766 : Nat := 118140960795 + 7003766 * 2 ^ 59
def prefixEnd_7003766 : Nat := 4983230072969 + 3 ^ 40 * 7003766 * 2
def baseEnd_7003766 : Nat := 3596298349617549967015273

theorem tailTrace_7003766 : CollatzResearch.WordTrace tailWord_7003766 prefixEnd_7003766 3596298349617549967015273 := by
  unfold tailWord_7003766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15965520746534962802981447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170298887963039603231802101 15965520746534962802981447)
  ·
    refine ⟨23948281119802444204472171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15965520746534962802981447 23948281119802444204472171)
    ·
      refine ⟨35922421679703666306708257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23948281119802444204472171 35922421679703666306708257)
      ·
        refine ⟨26941816259777749730031193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35922421679703666306708257 26941816259777749730031193)
        ·
          refine ⟨20206362194833312297523395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26941816259777749730031193 20206362194833312297523395)
          ·
            refine ⟨30309543292249968446285093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20206362194833312297523395 30309543292249968446285093)
            ·
              refine ⟨5683039367296869083678455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30309543292249968446285093 5683039367296869083678455)
              ·
                refine ⟨8524559050945303625517683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683039367296869083678455 8524559050945303625517683)
                ·
                  refine ⟨12786838576417955438276525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524559050945303625517683 12786838576417955438276525)
                  ·
                    refine ⟨4795064466156733289353697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12786838576417955438276525 4795064466156733289353697)
                    ·
                      refine ⟨3596298349617549967015273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795064466156733289353697 3596298349617549967015273)
                      ·
                        rfl

theorem cell23_7003766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_7003766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003766 prefixEnd_7003766 := by exact prefixLift 7003766
  have htrace : WordTrace (prefixWord ++ tailWord_7003766) baseStart_7003766 baseEnd_7003766 := by
    simpa [prefixWord, tailWord_7003766, baseEnd_7003766] using wordTrace_append hprefix tailTrace_7003766
  have hstable : (prefixWord ++ tailWord_7003766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003766).length < 2 ^ (prefixWord ++ tailWord_7003766).sum := by decide
  have hdescent : baseEnd_7003766 < baseStart_7003766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003785 : List Nat := [1, 2, 1, 1, 4, 1, 4, 4, 5]
def baseStart_7003785 : Nat := 118140960795 + 7003785 * 2 ^ 59
def prefixEnd_7003785 : Nat := 4983230072969 + 3 ^ 40 * 7003785 * 2
def baseEnd_7003785 : Nat := 399589789527776154741965

theorem tailTrace_7003785 : CollatzResearch.WordTrace tailWord_7003785 prefixEnd_7003785 399589789527776154741965 := by
  unfold tailWord_7003785
  simp only [CollatzResearch.WordTrace]
  refine ⟨255449024931490571092644809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170299349954327047395096539 255449024931490571092644809)
  ·
    refine ⟨191586768698617928319483607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255449024931490571092644809 191586768698617928319483607)
    ·
      refine ⟨287380153047926892479225411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191586768698617928319483607 287380153047926892479225411)
      ·
        refine ⟨431070229571890338718838117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287380153047926892479225411 431070229571890338718838117)
        ·
          refine ⟨80825668044729438509782147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431070229571890338718838117 80825668044729438509782147)
          ·
            refine ⟨121238502067094157764673221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80825668044729438509782147 121238502067094157764673221)
            ·
              refine ⟨22732219137580154580876229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121238502067094157764673221 22732219137580154580876229)
              ·
                refine ⟨4262291088296278983914293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22732219137580154580876229 4262291088296278983914293)
                ·
                  refine ⟨399589789527776154741965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4262291088296278983914293 399589789527776154741965)
                  ·
                    rfl

theorem cell23_7003785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 5].length) (baseStart_7003785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003785 prefixEnd_7003785 := by exact prefixLift 7003785
  have htrace : WordTrace (prefixWord ++ tailWord_7003785) baseStart_7003785 baseEnd_7003785 := by
    simpa [prefixWord, tailWord_7003785, baseEnd_7003785] using wordTrace_append hprefix tailTrace_7003785
  have hstable : (prefixWord ++ tailWord_7003785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003785).length < 2 ^ (prefixWord ++ tailWord_7003785).sum := by decide
  have hdescent : baseEnd_7003785 < baseStart_7003785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003796 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_7003796 : Nat := 118140960795 + 7003796 * 2 ^ 59
def prefixEnd_7003796 : Nat := 4983230072969 + 3 ^ 40 * 7003796 * 2
def baseEnd_7003796 : Nat := 3596313754037184849640135

theorem tailTrace_7003796 : CollatzResearch.WordTrace tailWord_7003796 prefixEnd_7003796 3596313754037184849640135 := by
  unfold tailWord_7003796
  simp only [CollatzResearch.WordTrace]
  refine ⟨127724713067225359985647621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170299617422967146647530161 127724713067225359985647621)
  ·
    refine ⟨23948383700104754997308929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127724713067225359985647621 23948383700104754997308929)
    ·
      refine ⟨17961287775078566247981697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23948383700104754997308929 17961287775078566247981697)
      ·
        refine ⟨13470965831308924685986273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17961287775078566247981697 13470965831308924685986273)
        ·
          refine ⟨10103224373481693514489705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13470965831308924685986273 10103224373481693514489705)
          ·
            refine ⟨7577418280111270135867279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10103224373481693514489705 7577418280111270135867279)
            ·
              refine ⟨11366127420166905203800919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7577418280111270135867279 11366127420166905203800919)
              ·
                refine ⟨17049191130250357805701379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11366127420166905203800919 17049191130250357805701379)
                ·
                  refine ⟨25573786695375536708552069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17049191130250357805701379 25573786695375536708552069)
                  ·
                    refine ⟨4795085005382913132853513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25573786695375536708552069 4795085005382913132853513)
                    ·
                      refine ⟨3596313754037184849640135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795085005382913132853513 3596313754037184849640135)
                      ·
                        rfl

theorem cell23_7003796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_7003796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003796 prefixEnd_7003796 := by exact prefixLift 7003796
  have htrace : WordTrace (prefixWord ++ tailWord_7003796) baseStart_7003796 baseEnd_7003796 := by
    simpa [prefixWord, tailWord_7003796, baseEnd_7003796] using wordTrace_append hprefix tailTrace_7003796
  have hstable : (prefixWord ++ tailWord_7003796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003796).length < 2 ^ (prefixWord ++ tailWord_7003796).sum := by decide
  have hdescent : baseEnd_7003796 < baseStart_7003796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003835 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 4, 4, 2]
def baseStart_7003835 : Nat := 118140960795 + 7003835 * 2 ^ 59
def prefixEnd_7003835 : Nat := 4983230072969 + 3 ^ 40 * 7003835 * 2
def baseEnd_7003835 : Nat := 3596333779782710197052455

theorem tailTrace_7003835 : CollatzResearch.WordTrace tailWord_7003835 prefixEnd_7003835 3596333779782710197052455 := by
  unfold tailWord_7003835
  simp only [CollatzResearch.WordTrace]
  refine ⟨255450848581309429631964959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170300565720872953087976639 255450848581309429631964959)
  ·
    refine ⟨383176272871964144447947439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255450848581309429631964959 383176272871964144447947439)
    ·
      refine ⟨574764409307946216671921159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383176272871964144447947439 574764409307946216671921159)
      ·
        refine ⟨862146613961919325007881739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574764409307946216671921159 862146613961919325007881739)
        ·
          refine ⟨1293219920942878987511822609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862146613961919325007881739 1293219920942878987511822609)
          ·
            refine ⟨969914940707159240633866957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293219920942878987511822609 969914940707159240633866957)
            ·
              refine ⟨363718102765184715237700109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 969914940707159240633866957 363718102765184715237700109)
              ·
                refine ⟨136394288536944268214137541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363718102765184715237700109 136394288536944268214137541)
                ·
                  refine ⟨25573929100677050290150789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136394288536944268214137541 25573929100677050290150789)
                  ·
                    refine ⟨4795111706376946929403273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25573929100677050290150789 4795111706376946929403273)
                    ·
                      refine ⟨3596333779782710197052455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795111706376946929403273 3596333779782710197052455)
                      ·
                        rfl

theorem cell23_7003835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 4, 2].length) (baseStart_7003835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003835 prefixEnd_7003835 := by exact prefixLift 7003835
  have htrace : WordTrace (prefixWord ++ tailWord_7003835) baseStart_7003835 baseEnd_7003835 := by
    simpa [prefixWord, tailWord_7003835, baseEnd_7003835] using wordTrace_append hprefix tailTrace_7003835
  have hstable : (prefixWord ++ tailWord_7003835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003835).length < 2 ^ (prefixWord ++ tailWord_7003835).sum := by decide
  have hdescent : baseEnd_7003835 < baseStart_7003835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003905 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7003905 : Nat := 118140960795 + 7003905 * 2 ^ 59
def prefixEnd_7003905 : Nat := 4983230072969 + 3 ^ 40 * 7003905 * 2
def baseEnd_7003905 : Nat := 1198789907809508307725711

theorem tailTrace_7003905 : CollatzResearch.WordTrace tailWord_7003905 prefixEnd_7003905 1198789907809508307725711 := by
  unfold tailWord_7003905
  simp only [CollatzResearch.WordTrace]
  refine ⟨255453401691055831587013169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170302267794037221058008779 255453401691055831587013169)
  ·
    refine ⟨191590051268291873690259877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255453401691055831587013169 191590051268291873690259877)
    ·
      refine ⟨35923134612804726316923727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191590051268291873690259877 35923134612804726316923727)
      ·
        refine ⟨53884701919207089475385591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35923134612804726316923727 53884701919207089475385591)
        ·
          refine ⟨80827052878810634213078387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53884701919207089475385591 80827052878810634213078387)
          ·
            refine ⟨121240579318215951319617581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80827052878810634213078387 121240579318215951319617581)
            ·
              refine ⟨45465217244330981744856593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121240579318215951319617581 45465217244330981744856593)
              ·
                refine ⟨34098912933248236308642445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45465217244330981744856593 34098912933248236308642445)
                ·
                  refine ⟨12787092349968088615740917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34098912933248236308642445 12787092349968088615740917)
                  ·
                    refine ⟨1198789907809508307725711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12787092349968088615740917 1198789907809508307725711)
                    ·
                      rfl

theorem cell23_7003905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7003905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003905 prefixEnd_7003905 := by exact prefixLift 7003905
  have htrace : WordTrace (prefixWord ++ tailWord_7003905) baseStart_7003905 baseEnd_7003905 := by
    simpa [prefixWord, tailWord_7003905, baseEnd_7003905] using wordTrace_append hprefix tailTrace_7003905
  have hstable : (prefixWord ++ tailWord_7003905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003905).length < 2 ^ (prefixWord ++ tailWord_7003905).sum := by decide
  have hdescent : baseEnd_7003905 < baseStart_7003905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003912 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_7003912 : Nat := 118140960795 + 7003912 * 2 ^ 59
def prefixEnd_7003912 : Nat := 4983230072969 + 3 ^ 40 * 7003912 * 2
def baseEnd_7003912 : Nat := 3596373317793106395789601

theorem tailTrace_7003912 : CollatzResearch.WordTrace tailWord_7003912 prefixEnd_7003912 3596373317793106395789601 := by
  unfold tailWord_7003912
  simp only [CollatzResearch.WordTrace]
  refine ⟨127726828501015235891258995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170302438001353647855011993 127726828501015235891258995)
  ·
    refine ⟨191590242751522853836888493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127726828501015235891258995 191590242751522853836888493)
    ·
      refine ⟨71846341031821070188833185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191590242751522853836888493 71846341031821070188833185)
      ·
        refine ⟨53884755773865802641624889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71846341031821070188833185 53884755773865802641624889)
        ·
          refine ⟨40413566830399351981218667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53884755773865802641624889 40413566830399351981218667)
          ·
            refine ⟨60620350245599027971828001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40413566830399351981218667 60620350245599027971828001)
            ·
              refine ⟨45465262684199270978871001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60620350245599027971828001 45465262684199270978871001)
              ·
                refine ⟨34098947013149453234153251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45465262684199270978871001 34098947013149453234153251)
                ·
                  refine ⟨51148420519724179851229877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34098947013149453234153251 51148420519724179851229877)
                  ·
                    refine ⟨4795164423724141861052801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51148420519724179851229877 4795164423724141861052801)
                    ·
                      refine ⟨3596373317793106395789601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795164423724141861052801 3596373317793106395789601)
                      ·
                        rfl

theorem cell23_7003912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_7003912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003912 prefixEnd_7003912 := by exact prefixLift 7003912
  have htrace : WordTrace (prefixWord ++ tailWord_7003912) baseStart_7003912 baseEnd_7003912 := by
    simpa [prefixWord, tailWord_7003912, baseEnd_7003912] using wordTrace_append hprefix tailTrace_7003912
  have hstable : (prefixWord ++ tailWord_7003912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003912).length < 2 ^ (prefixWord ++ tailWord_7003912).sum := by decide
  have hdescent : baseEnd_7003912 < baseStart_7003912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003935 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 1, 6]
def baseStart_7003935 : Nat := 118140960795 + 7003935 * 2 ^ 59
def prefixEnd_7003935 : Nat := 4983230072969 + 3 ^ 40 * 7003935 * 2
def baseEnd_7003935 : Nat := 1198795042616053268600665

theorem tailTrace_7003935 : CollatzResearch.WordTrace tailWord_7003935 prefixEnd_7003935 1198795042616053268600665 := by
  unfold tailWord_7003935
  simp only [CollatzResearch.WordTrace]
  refine ⟨255454495880947146710605259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170302997253964764473736839 255454495880947146710605259)
  ·
    refine ⟨383181743821420720065907889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255454495880947146710605259 383181743821420720065907889)
    ·
      refine ⟨287386307866065540049430917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383181743821420720065907889 287386307866065540049430917)
      ·
        refine ⟨53884932724887288759268297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287386307866065540049430917 53884932724887288759268297)
        ·
          refine ⟨40413699543665466569451223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53884932724887288759268297 40413699543665466569451223)
          ·
            refine ⟨60620549315498199854176835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40413699543665466569451223 60620549315498199854176835)
            ·
              refine ⟨90930823973247299781265253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60620549315498199854176835 90930823973247299781265253)
              ·
                refine ⟨17049529494983868708987235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90930823973247299781265253 17049529494983868708987235)
                ·
                  refine ⟨25574294242475803063480853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17049529494983868708987235 25574294242475803063480853)
                  ·
                    refine ⟨1198795042616053268600665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25574294242475803063480853 1198795042616053268600665)
                    ·
                      rfl

theorem cell23_7003935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_7003935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003935 prefixEnd_7003935 := by exact prefixLift 7003935
  have htrace : WordTrace (prefixWord ++ tailWord_7003935) baseStart_7003935 baseEnd_7003935 := by
    simpa [prefixWord, tailWord_7003935, baseEnd_7003935] using wordTrace_append hprefix tailTrace_7003935
  have hstable : (prefixWord ++ tailWord_7003935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003935).length < 2 ^ (prefixWord ++ tailWord_7003935).sum := by decide
  have hdescent : baseEnd_7003935 < baseStart_7003935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003936 : List Nat := [2, 1, 1, 5, 1, 1, 4, 3, 1, 1, 3]
def baseStart_7003936 : Nat := 118140960795 + 7003936 * 2 ^ 59
def prefixEnd_7003936 : Nat := 4983230072969 + 3 ^ 40 * 7003936 * 2
def baseEnd_7003936 : Nat := 3596385641328814301889491

theorem tailTrace_7003936 : CollatzResearch.WordTrace tailWord_7003936 prefixEnd_7003936 3596385641328814301889491 := by
  unfold tailWord_7003936
  simp only [CollatzResearch.WordTrace]
  refine ⟨127727266176971761940695831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170303021569295682587594441 127727266176971761940695831)
  ·
    refine ⟨191590899265457642911043747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127727266176971761940695831 191590899265457642911043747)
    ·
      refine ⟨287386348898186464366565621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191590899265457642911043747 287386348898186464366565621)
      ·
        refine ⟨26942470209204981034365527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 287386348898186464366565621 26942470209204981034365527)
        ·
          refine ⟨40413705313807471551548291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26942470209204981034365527 40413705313807471551548291)
          ·
            refine ⟨60620557970711207327322437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40413705313807471551548291 60620557970711207327322437)
            ·
              refine ⟨11366354619508351373872957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60620557970711207327322437 11366354619508351373872957)
              ·
                refine ⟨4262382982315631765202359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11366354619508351373872957 4262382982315631765202359)
                ·
                  refine ⟨6393574473473447647803539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262382982315631765202359 6393574473473447647803539)
                  ·
                    refine ⟨9590361710210171471705309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6393574473473447647803539 9590361710210171471705309)
                    ·
                      refine ⟨3596385641328814301889491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9590361710210171471705309 3596385641328814301889491)
                      ·
                        rfl

theorem cell23_7003936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_7003936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003936 prefixEnd_7003936 := by exact prefixLift 7003936
  have htrace : WordTrace (prefixWord ++ tailWord_7003936) baseStart_7003936 baseEnd_7003936 := by
    simpa [prefixWord, tailWord_7003936, baseEnd_7003936] using wordTrace_append hprefix tailTrace_7003936
  have hstable : (prefixWord ++ tailWord_7003936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003936).length < 2 ^ (prefixWord ++ tailWord_7003936).sum := by decide
  have hdescent : baseEnd_7003936 < baseStart_7003936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7003962 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_7003962 : Nat := 118140960795 + 7003962 * 2 ^ 59
def prefixEnd_7003962 : Nat := 4983230072969 + 3 ^ 40 * 7003962 * 2
def baseEnd_7003962 : Nat := 3596398991825831200164371

theorem tailTrace_7003962 : CollatzResearch.WordTrace tailWord_7003962 prefixEnd_7003962 3596398991825831200164371 := by
  unfold tailWord_7003962
  simp only [CollatzResearch.WordTrace]
  refine ⟨63863870162962332580459535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170303653767899553547892093 63863870162962332580459535)
  ·
    refine ⟨95795805244443498870689303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63863870162962332580459535 95795805244443498870689303)
    ·
      refine ⟨143693707866665248306033955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95795805244443498870689303 143693707866665248306033955)
      ·
        refine ⟨215540561799997872459050933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143693707866665248306033955 215540561799997872459050933)
        ·
          refine ⟨20206927668749800543036025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215540561799997872459050933 20206927668749800543036025)
          ·
            refine ⟨15155195751562350407277019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20206927668749800543036025 15155195751562350407277019)
            ·
              refine ⟨22732793627343525610915529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15155195751562350407277019 22732793627343525610915529)
              ·
                refine ⟨17049595220507644208186647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22732793627343525610915529 17049595220507644208186647)
                ·
                  refine ⟨25574392830761466312279971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17049595220507644208186647 25574392830761466312279971)
                  ·
                    refine ⟨38361589246142199468419957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25574392830761466312279971 38361589246142199468419957)
                    ·
                      refine ⟨3596398991825831200164371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38361589246142199468419957 3596398991825831200164371)
                      ·
                        rfl

theorem cell23_7003962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_7003962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7003962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7003962 prefixEnd_7003962 := by exact prefixLift 7003962
  have htrace : WordTrace (prefixWord ++ tailWord_7003962) baseStart_7003962 baseEnd_7003962 := by
    simpa [prefixWord, tailWord_7003962, baseEnd_7003962] using wordTrace_append hprefix tailTrace_7003962
  have hstable : (prefixWord ++ tailWord_7003962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7003962).length < 2 ^ (prefixWord ++ tailWord_7003962).sum := by decide
  have hdescent : baseEnd_7003962 < baseStart_7003962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7003962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004005 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_7004005 : Nat := 118140960795 + 7004005 * 2 ^ 59
def prefixEnd_7004005 : Nat := 4983230072969 + 3 ^ 40 * 7004005 * 2
def baseEnd_7004005 : Nat := 3596421071493974531926673

theorem tailTrace_7004005 : CollatzResearch.WordTrace tailWord_7004005 prefixEnd_7004005 3596421071493974531926673 := by
  unfold tailWord_7004005
  simp only [CollatzResearch.WordTrace]
  refine ⟨255457048990693548665653469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170304699327129032443768979 255457048990693548665653469)
  ·
    refine ⟨95796393371510080749620051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255457048990693548665653469 95796393371510080749620051)
    ·
      refine ⟨143694590057265121124430077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95796393371510080749620051 143694590057265121124430077)
      ·
        refine ⟨53885471271474420421661279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143694590057265121124430077 53885471271474420421661279)
        ·
          refine ⟨80828206907211630632491919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53885471271474420421661279 80828206907211630632491919)
          ·
            refine ⟨121242310360817445948737879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80828206907211630632491919 121242310360817445948737879)
            ·
              refine ⟨181863465541226168923106819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121242310360817445948737879 181863465541226168923106819)
              ·
                refine ⟨272795198311839253384660229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181863465541226168923106819 272795198311839253384660229)
                ·
                  refine ⟨51149099683469860009623793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272795198311839253384660229 51149099683469860009623793)
                  ·
                    refine ⟨38361824762602395007217845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51149099683469860009623793 38361824762602395007217845)
                    ·
                      refine ⟨3596421071493974531926673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38361824762602395007217845 3596421071493974531926673)
                      ·
                        rfl

theorem cell23_7004005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_7004005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004005 prefixEnd_7004005 := by exact prefixLift 7004005
  have htrace : WordTrace (prefixWord ++ tailWord_7004005) baseStart_7004005 baseEnd_7004005 := by
    simpa [prefixWord, tailWord_7004005, baseEnd_7004005] using wordTrace_append hprefix tailTrace_7004005
  have hstable : (prefixWord ++ tailWord_7004005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004005).length < 2 ^ (prefixWord ++ tailWord_7004005).sum := by decide
  have hdescent : baseEnd_7004005 < baseStart_7004005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004010 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7004010 : Nat := 118140960795 + 7004010 * 2 ^ 59
def prefixEnd_7004010 : Nat := 4983230072969 + 3 ^ 40 * 7004010 * 2
def baseEnd_7004010 : Nat := 3596423638897247012364151

theorem tailTrace_7004010 : CollatzResearch.WordTrace tailWord_7004010 prefixEnd_7004010 3596423638897247012364151 := by
  unfold tailWord_7004010
  simp only [CollatzResearch.WordTrace]
  refine ⟨63864307838918858629896371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170304820903783623013056989 63864307838918858629896371)
  ·
    refine ⟨95796461758378287944844557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63864307838918858629896371 95796461758378287944844557)
    ·
      refine ⟨35923673159391857979316709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95796461758378287944844557 35923673159391857979316709)
      ·
        refine ⟨6735688717385973371121883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35923673159391857979316709 6735688717385973371121883)
        ·
          refine ⟨10103533076078960056682825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6735688717385973371121883 10103533076078960056682825)
          ·
            refine ⟨7577649807059220042512119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10103533076078960056682825 7577649807059220042512119)
            ·
              refine ⟨11366474710588830063768179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7577649807059220042512119 11366474710588830063768179)
              ·
                refine ⟨17049712065883245095652269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11366474710588830063768179 17049712065883245095652269)
                ·
                  refine ⟨6393642024706216910869601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17049712065883245095652269 6393642024706216910869601)
                  ·
                    refine ⟨4795231518529662683152201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6393642024706216910869601 4795231518529662683152201)
                    ·
                      refine ⟨3596423638897247012364151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795231518529662683152201 3596423638897247012364151)
                      ·
                        rfl

theorem cell23_7004010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7004010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004010 prefixEnd_7004010 := by exact prefixLift 7004010
  have htrace : WordTrace (prefixWord ++ tailWord_7004010) baseStart_7004010 baseEnd_7004010 := by
    simpa [prefixWord, tailWord_7004010, baseEnd_7004010] using wordTrace_append hprefix tailTrace_7004010
  have hstable : (prefixWord ++ tailWord_7004010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004010).length < 2 ^ (prefixWord ++ tailWord_7004010).sum := by decide
  have hdescent : baseEnd_7004010 < baseStart_7004010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004025 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 1, 8]
def baseStart_7004025 : Nat := 118140960795 + 7004025 * 2 ^ 59
def prefixEnd_7004025 : Nat := 4983230072969 + 3 ^ 40 * 7004025 * 2
def baseEnd_7004025 : Nat := 1198810447035688151225527

theorem tailTrace_7004025 : CollatzResearch.WordTrace tailWord_7004025 prefixEnd_7004025 1198810447035688151225527 := by
  unfold tailWord_7004025
  simp only [CollatzResearch.WordTrace]
  refine ⟨255457778450621092081381529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170305185633747394720921019 255457778450621092081381529)
  ·
    refine ⟨191593333837965819061036147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255457778450621092081381529 191593333837965819061036147)
    ·
      refine ⟨287390000756948728591554221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191593333837965819061036147 287390000756948728591554221)
      ·
        refine ⟨107771250283855773221832833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287390000756948728591554221 107771250283855773221832833)
        ·
          refine ⟨80828437712891829916374625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107771250283855773221832833 80828437712891829916374625)
          ·
            refine ⟨60621328284668872437280969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80828437712891829916374625 60621328284668872437280969)
            ·
              refine ⟨45465996213501654327960727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60621328284668872437280969 45465996213501654327960727)
              ·
                refine ⟨68198994320252481491941091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45465996213501654327960727 68198994320252481491941091)
                ·
                  refine ⟨102298491480378722237911637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68198994320252481491941091 102298491480378722237911637)
                  ·
                    refine ⟨1198810447035688151225527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102298491480378722237911637 1198810447035688151225527)
                    ·
                      rfl

theorem cell23_7004025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_7004025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004025 prefixEnd_7004025 := by exact prefixLift 7004025
  have htrace : WordTrace (prefixWord ++ tailWord_7004025) baseStart_7004025 baseEnd_7004025 := by
    simpa [prefixWord, tailWord_7004025, baseEnd_7004025] using wordTrace_append hprefix tailTrace_7004025
  have hstable : (prefixWord ++ tailWord_7004025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004025).length < 2 ^ (prefixWord ++ tailWord_7004025).sum := by decide
  have hdescent : baseEnd_7004025 < baseStart_7004025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004026 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3]
def baseStart_7004026 : Nat := 118140960795 + 7004026 * 2 ^ 59
def prefixEnd_7004026 : Nat := 4983230072969 + 3 ^ 40 * 7004026 * 2
def baseEnd_7004026 : Nat := 3596431854587718949764077

theorem tailTrace_7004026 : CollatzResearch.WordTrace tailWord_7004026 prefixEnd_7004026 3596431854587718949764077 := by
  unfold tailWord_7004026
  simp only [CollatzResearch.WordTrace]
  refine ⟨63864453730904367313041983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170305209949078312834778621 63864453730904367313041983)
  ·
    refine ⟨95796680596356550969562975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63864453730904367313041983 95796680596356550969562975)
    ·
      refine ⟨143695020894534826454344463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95796680596356550969562975 143695020894534826454344463)
      ·
        refine ⟨215542531341802239681516695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143695020894534826454344463 215542531341802239681516695)
        ·
          refine ⟨323313797012703359522275043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215542531341802239681516695 323313797012703359522275043)
          ·
            refine ⟨484970695519055039283412565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323313797012703359522275043 484970695519055039283412565)
            ·
              refine ⟨5683250338113926241602491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 484970695519055039283412565 5683250338113926241602491)
              ·
                refine ⟨8524875507170889362403737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683250338113926241602491 8524875507170889362403737)
                ·
                  refine ⟨6393656630378167021802803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8524875507170889362403737 6393656630378167021802803)
                  ·
                    refine ⟨9590484945567250532704205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6393656630378167021802803 9590484945567250532704205)
                    ·
                      refine ⟨3596431854587718949764077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9590484945567250532704205 3596431854587718949764077)
                      ·
                        rfl

theorem cell23_7004026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_7004026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004026 prefixEnd_7004026 := by exact prefixLift 7004026
  have htrace : WordTrace (prefixWord ++ tailWord_7004026) baseStart_7004026 baseEnd_7004026 := by
    simpa [prefixWord, tailWord_7004026, baseEnd_7004026] using wordTrace_append hprefix tailTrace_7004026
  have hstable : (prefixWord ++ tailWord_7004026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004026).length < 2 ^ (prefixWord ++ tailWord_7004026).sum := by decide
  have hdescent : baseEnd_7004026 < baseStart_7004026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004036 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_7004036 : Nat := 118140960795 + 7004036 * 2 ^ 59
def prefixEnd_7004036 : Nat := 4983230072969 + 3 ^ 40 * 7004036 * 2
def baseEnd_7004036 : Nat := 3596436989394263910639031

theorem tailTrace_7004036 : CollatzResearch.WordTrace tailWord_7004036 prefixEnd_7004036 3596436989394263910639031 := by
  unfold tailWord_7004036
  simp only [CollatzResearch.WordTrace]
  refine ⟨127729089826790620480015981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170305453102387493973354641 127729089826790620480015981)
  ·
    refine ⟨47898408685046482680005993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127729089826790620480015981 47898408685046482680005993)
    ·
      refine ⟨35923806513784862010004495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47898408685046482680005993 35923806513784862010004495)
      ·
        refine ⟨53885709770677293015006743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35923806513784862010004495 53885709770677293015006743)
        ·
          refine ⟨80828564656015939522510115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53885709770677293015006743 80828564656015939522510115)
          ·
            refine ⟨121242846984023909283765173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80828564656015939522510115 121242846984023909283765173)
            ·
              refine ⟨11366516904752241495352985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121242846984023909283765173 11366516904752241495352985)
              ·
                refine ⟨8524887678564181121514739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11366516904752241495352985 8524887678564181121514739)
                ·
                  refine ⟨12787331517846271682272109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524887678564181121514739 12787331517846271682272109)
                  ·
                    refine ⟨4795249319192351880852041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12787331517846271682272109 4795249319192351880852041)
                    ·
                      refine ⟨3596436989394263910639031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795249319192351880852041 3596436989394263910639031)
                      ·
                        rfl

theorem cell23_7004036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_7004036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004036 prefixEnd_7004036 := by exact prefixLift 7004036
  have htrace : WordTrace (prefixWord ++ tailWord_7004036) baseStart_7004036 baseEnd_7004036 := by
    simpa [prefixWord, tailWord_7004036, baseEnd_7004036] using wordTrace_append hprefix tailTrace_7004036
  have hstable : (prefixWord ++ tailWord_7004036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004036).length < 2 ^ (prefixWord ++ tailWord_7004036).sum := by decide
  have hdescent : baseEnd_7004036 < baseStart_7004036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004049 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 6, 2, 2]
def baseStart_7004049 : Nat := 118140960795 + 7004049 * 2 ^ 59
def prefixEnd_7004049 : Nat := 4983230072969 + 3 ^ 40 * 7004049 * 2
def baseEnd_7004049 : Nat := 3596443664642772359776471

theorem tailTrace_7004049 : CollatzResearch.WordTrace tailWord_7004049 prefixEnd_7004049 3596443664642772359776471 := by
  unfold tailWord_7004049
  simp only [CollatzResearch.WordTrace]
  refine ⟨255458653802534144180255201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170305769201689429453503467 255458653802534144180255201)
  ·
    refine ⟨191593990351900608135191401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255458653802534144180255201 191593990351900608135191401)
    ·
      refine ⟨143695492763925456101393551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191593990351900608135191401 143695492763925456101393551)
      ·
        refine ⟨215543239145888184152090327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143695492763925456101393551 215543239145888184152090327)
        ·
          refine ⟨323314858718832276228135491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215543239145888184152090327 323314858718832276228135491)
          ·
            refine ⟨484972288078248414342203237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323314858718832276228135491 484972288078248414342203237)
            ·
              refine ⟨90932304014671577689163107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 484972288078248414342203237 90932304014671577689163107)
              ·
                refine ⟨136398456022007366533744661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90932304014671577689163107 136398456022007366533744661)
                ·
                  refine ⟨6393677626031595306269281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136398456022007366533744661 6393677626031595306269281)
                  ·
                    refine ⟨4795258219523696479701961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6393677626031595306269281 4795258219523696479701961)
                    ·
                      refine ⟨3596443664642772359776471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795258219523696479701961 3596443664642772359776471)
                      ·
                        rfl

theorem cell23_7004049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_7004049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004049 prefixEnd_7004049 := by exact prefixLift 7004049
  have htrace : WordTrace (prefixWord ++ tailWord_7004049) baseStart_7004049 baseEnd_7004049 := by
    simpa [prefixWord, tailWord_7004049, baseEnd_7004049] using wordTrace_append hprefix tailTrace_7004049
  have hstable : (prefixWord ++ tailWord_7004049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004049).length < 2 ^ (prefixWord ++ tailWord_7004049).sum := by decide
  have hdescent : baseEnd_7004049 < baseStart_7004049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004183 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 3, 4]
def baseStart_7004183 : Nat := 118140960795 + 7004183 * 2 ^ 59
def prefixEnd_7004183 : Nat := 4983230072969 + 3 ^ 40 * 7004183 * 2
def baseEnd_7004183 : Nat := 1198837490350158278500285

theorem tailTrace_7004183 : CollatzResearch.WordTrace tailWord_7004183 prefixEnd_7004183 1198837490350158278500285 := by
  unfold tailWord_7004183
  simp only [CollatzResearch.WordTrace]
  refine ⟨255463541184048685065633203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170309027456032456710422135 255463541184048685065633203)
  ·
    refine ⟨383195311776073027598449805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255463541184048685065633203 383195311776073027598449805)
    ·
      refine ⟨143698241916027385349418677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383195311776073027598449805 143698241916027385349418677)
      ·
        refine ⟨13471710179627567376508001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143698241916027385349418677 13471710179627567376508001)
        ·
          refine ⟨10103782634720675532381001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13471710179627567376508001 10103782634720675532381001)
          ·
            refine ⟨7577836976040506649285751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10103782634720675532381001 7577836976040506649285751)
            ·
              refine ⟨11366755464060759973928627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7577836976040506649285751 11366755464060759973928627)
              ·
                refine ⟨17050133196091139960892941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11366755464060759973928627 17050133196091139960892941)
                ·
                  refine ⟨6393799948534177485334853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17050133196091139960892941 6393799948534177485334853)
                  ·
                    refine ⟨1198837490350158278500285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6393799948534177485334853 1198837490350158278500285)
                    ·
                      rfl

theorem cell23_7004183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_7004183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004183 prefixEnd_7004183 := by exact prefixLift 7004183
  have htrace : WordTrace (prefixWord ++ tailWord_7004183) baseStart_7004183 baseEnd_7004183 := by
    simpa [prefixWord, tailWord_7004183, baseEnd_7004183] using wordTrace_append hprefix tailTrace_7004183
  have hstable : (prefixWord ++ tailWord_7004183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004183).length < 2 ^ (prefixWord ++ tailWord_7004183).sum := by decide
  have hdescent : baseEnd_7004183 < baseStart_7004183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004196 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 6]
def baseStart_7004196 : Nat := 118140960795 + 7004196 * 2 ^ 59
def prefixEnd_7004196 : Nat := 4983230072969 + 3 ^ 40 * 7004196 * 2
def baseEnd_7004196 : Nat := 399613238477664809404255

theorem tailTrace_7004196 : CollatzResearch.WordTrace tailWord_7004196 prefixEnd_7004196 399613238477664809404255 := by
  unfold tailWord_7004196
  simp only [CollatzResearch.WordTrace]
  refine ⟨127732007666500794142928221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170309343555334392190570961 127732007666500794142928221)
  ·
    refine ⟨47899502874937797803598083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127732007666500794142928221 47899502874937797803598083)
    ·
      refine ⟨71849254312406696705397125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47899502874937797803598083 71849254312406696705397125)
      ·
        refine ⟨13471735183576255632261961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71849254312406696705397125 13471735183576255632261961)
        ·
          refine ⟨10103801387682191724196471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13471735183576255632261961 10103801387682191724196471)
          ·
            refine ⟨15155702081523287586294707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10103801387682191724196471 15155702081523287586294707)
            ·
              refine ⟨22733553122284931379442061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15155702081523287586294707 22733553122284931379442061)
              ·
                refine ⟨8525082420856849267290773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22733553122284931379442061 8525082420856849267290773)
                ·
                  refine ⟨399613238477664809404255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8525082420856849267290773 399613238477664809404255)
                  ·
                    rfl

theorem cell23_7004196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_7004196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004196 prefixEnd_7004196 := by exact prefixLift 7004196
  have htrace : WordTrace (prefixWord ++ tailWord_7004196) baseStart_7004196 baseEnd_7004196 := by
    simpa [prefixWord, tailWord_7004196, baseEnd_7004196] using wordTrace_append hprefix tailTrace_7004196
  have hstable : (prefixWord ++ tailWord_7004196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004196).length < 2 ^ (prefixWord ++ tailWord_7004196).sum := by decide
  have hdescent : baseEnd_7004196 < baseStart_7004196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004209 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 3, 5]
def baseStart_7004209 : Nat := 118140960795 + 7004209 * 2 ^ 59
def prefixEnd_7004209 : Nat := 4983230072969 + 3 ^ 40 * 7004209 * 2
def baseEnd_7004209 : Nat := 1198841940515830577925245

theorem tailTrace_7004209 : CollatzResearch.WordTrace tailWord_7004209 prefixEnd_7004209 1198841940515830577925245 := by
  unfold tailWord_7004209
  simp only [CollatzResearch.WordTrace]
  refine ⟨255464489481954491506079681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170309659654636327670719787 255464489481954491506079681)
  ·
    refine ⟨191598367111465868629559761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255464489481954491506079681 191598367111465868629559761)
    ·
      refine ⟨143698775333599401472169821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191598367111465868629559761 143698775333599401472169821)
      ·
        refine ⟨53887040750099775552063683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143698775333599401472169821 53887040750099775552063683)
        ·
          refine ⟨80830561125149663328095525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53887040750099775552063683 80830561125149663328095525)
          ·
            refine ⟨15155730210965561874017911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80830561125149663328095525 15155730210965561874017911)
            ·
              refine ⟨22733595316448342811026867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15155730210965561874017911 22733595316448342811026867)
              ·
                refine ⟨34100392974672514216540301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22733595316448342811026867 34100392974672514216540301)
                ·
                  refine ⟨12787647365502192831202613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34100392974672514216540301 12787647365502192831202613)
                  ·
                    refine ⟨1198841940515830577925245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12787647365502192831202613 1198841940515830577925245)
                    ·
                      rfl

theorem cell23_7004209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_7004209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004209 prefixEnd_7004209 := by exact prefixLift 7004209
  have htrace : WordTrace (prefixWord ++ tailWord_7004209) baseStart_7004209 baseEnd_7004209 := by
    simpa [prefixWord, tailWord_7004209, baseEnd_7004209] using wordTrace_append hprefix tailTrace_7004209
  have hstable : (prefixWord ++ tailWord_7004209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004209).length < 2 ^ (prefixWord ++ tailWord_7004209).sum := by decide
  have hdescent : baseEnd_7004209 < baseStart_7004209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004249 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 3]
def baseStart_7004249 : Nat := 118140960795 + 7004249 * 2 ^ 59
def prefixEnd_7004249 : Nat := 4983230072969 + 3 ^ 40 * 7004249 * 2
def baseEnd_7004249 : Nat := 3596546360773671577275551

theorem tailTrace_7004249 : CollatzResearch.WordTrace tailWord_7004249 prefixEnd_7004249 3596546360773671577275551 := by
  unfold tailWord_7004249
  simp only [CollatzResearch.WordTrace]
  refine ⟨255465948401809578337535801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170310632267873052225023867 255465948401809578337535801)
  ·
    refine ⟨191599461301357183753151851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255465948401809578337535801 191599461301357183753151851)
    ·
      refine ⟨287399191952035775629727777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191599461301357183753151851 287399191952035775629727777)
      ·
        refine ⟨215549393964026831722295833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287399191952035775629727777 215549393964026831722295833)
        ·
          refine ⟨161662045473020123791721875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215549393964026831722295833 161662045473020123791721875)
          ·
            refine ⟨242493068209530185687582813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161662045473020123791721875 242493068209530185687582813)
            ·
              refine ⟨90934900578573819632843555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242493068209530185687582813 90934900578573819632843555)
              ·
                refine ⟨136402350867860729449265333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90934900578573819632843555 136402350867860729449265333)
                ·
                  refine ⟨12787720393861943385868625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136402350867860729449265333 12787720393861943385868625)
                  ·
                    refine ⟨9590790295396457539401469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12787720393861943385868625 9590790295396457539401469)
                    ·
                      refine ⟨3596546360773671577275551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9590790295396457539401469 3596546360773671577275551)
                      ·
                        rfl

theorem cell23_7004249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_7004249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004249 prefixEnd_7004249 := by exact prefixLift 7004249
  have htrace : WordTrace (prefixWord ++ tailWord_7004249) baseStart_7004249 baseEnd_7004249 := by
    simpa [prefixWord, tailWord_7004249, baseEnd_7004249] using wordTrace_append hprefix tailTrace_7004249
  have hstable : (prefixWord ++ tailWord_7004249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004249).length < 2 ^ (prefixWord ++ tailWord_7004249).sum := by decide
  have hdescent : baseEnd_7004249 < baseStart_7004249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004256 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 2, 4]
def baseStart_7004256 : Nat := 118140960795 + 7004256 * 2 ^ 59
def prefixEnd_7004256 : Nat := 4983230072969 + 3 ^ 40 * 7004256 * 2
def baseEnd_7004256 : Nat := 1198849985046084349962673

theorem tailTrace_7004256 : CollatzResearch.WordTrace tailWord_7004256 prefixEnd_7004256 1198849985046084349962673 := by
  unfold tailWord_7004256
  simp only [CollatzResearch.WordTrace]
  refine ⟨127733101856392109266520311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170310802475189479022027081 127733101856392109266520311)
  ·
    refine ⟨191599652784588163899780467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127733101856392109266520311 191599652784588163899780467)
    ·
      refine ⟨287399479176882245849670701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191599652784588163899780467 287399479176882245849670701)
      ·
        refine ⟨107774804691330842193626513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287399479176882245849670701 107774804691330842193626513)
        ·
          refine ⟨80831103518498131645219885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107774804691330842193626513 80831103518498131645219885)
          ·
            refine ⟨30311663819436799366957457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80831103518498131645219885 30311663819436799366957457)
            ·
              refine ⟨22733747864577599525218093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30311663819436799366957457 22733747864577599525218093)
              ·
                refine ⟨8525155449216599821956785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22733747864577599525218093 8525155449216599821956785)
                ·
                  refine ⟨6393866586912449866467589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8525155449216599821956785 6393866586912449866467589)
                  ·
                    refine ⟨1198849985046084349962673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6393866586912449866467589 1198849985046084349962673)
                    ·
                      rfl

theorem cell23_7004256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 4].length) (baseStart_7004256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004256 prefixEnd_7004256 := by exact prefixLift 7004256
  have htrace : WordTrace (prefixWord ++ tailWord_7004256) baseStart_7004256 baseEnd_7004256 := by
    simpa [prefixWord, tailWord_7004256, baseEnd_7004256] using wordTrace_append hprefix tailTrace_7004256
  have hstable : (prefixWord ++ tailWord_7004256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004256).length < 2 ^ (prefixWord ++ tailWord_7004256).sum := by decide
  have hdescent : baseEnd_7004256 < baseStart_7004256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004259 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 4]
def baseStart_7004259 : Nat := 118140960795 + 7004259 * 2 ^ 59
def prefixEnd_7004259 : Nat := 4983230072969 + 3 ^ 40 * 7004259 * 2
def baseEnd_7004259 : Nat := 3596551495580216538150505

theorem tailTrace_7004259 : CollatzResearch.WordTrace tailWord_7004259 prefixEnd_7004259 3596551495580216538150505 := by
  unfold tailWord_7004259
  simp only [CollatzResearch.WordTrace]
  refine ⟨255466313131773350045399831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170310875421182233363599887 255466313131773350045399831)
  ·
    refine ⟨383199469697660025068099747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255466313131773350045399831 383199469697660025068099747)
    ·
      refine ⟨574799204546490037602149621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383199469697660025068099747 574799204546490037602149621)
      ·
        refine ⟨53887425426233441025201527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 574799204546490037602149621 53887425426233441025201527)
        ·
          refine ⟨80831138139350161537802291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53887425426233441025201527 80831138139350161537802291)
          ·
            refine ⟨121246707209025242306703437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80831138139350161537802291 121246707209025242306703437)
            ·
              refine ⟨45467515203384465865013789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121246707209025242306703437 45467515203384465865013789)
              ·
                refine ⟨17050318201269174699380171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45467515203384465865013789 17050318201269174699380171)
                ·
                  refine ⟨25575477301903762049070257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17050318201269174699380171 25575477301903762049070257)
                  ·
                    refine ⟨19181607976427821536802693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25575477301903762049070257 19181607976427821536802693)
                    ·
                      refine ⟨3596551495580216538150505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19181607976427821536802693 3596551495580216538150505)
                      ·
                        rfl

theorem cell23_7004259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_7004259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004259 prefixEnd_7004259 := by exact prefixLift 7004259
  have htrace : WordTrace (prefixWord ++ tailWord_7004259) baseStart_7004259 baseEnd_7004259 := by
    simpa [prefixWord, tailWord_7004259, baseEnd_7004259] using wordTrace_append hprefix tailTrace_7004259
  have hstable : (prefixWord ++ tailWord_7004259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004259).length < 2 ^ (prefixWord ++ tailWord_7004259).sum := by decide
  have hdescent : baseEnd_7004259 < baseStart_7004259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004263 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_7004263 : Nat := 118140960795 + 7004263 * 2 ^ 59
def prefixEnd_7004263 : Nat := 4983230072969 + 3 ^ 40 * 7004263 * 2
def baseEnd_7004263 : Nat := 3596553549502834522500487

theorem tailTrace_7004263 : CollatzResearch.WordTrace tailWord_7004263 prefixEnd_7004263 3596553549502834522500487 := by
  unfold tailWord_7004263
  simp only [CollatzResearch.WordTrace]
  refine ⟨255466459023758858728545443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170310972682505905819030295 255466459023758858728545443)
  ·
    refine ⟨383199688535638288092818165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255466459023758858728545443 383199688535638288092818165)
    ·
      refine ⟨35924970800216089508701703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 383199688535638288092818165 35924970800216089508701703)
      ·
        refine ⟨53887456200324134263052555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35924970800216089508701703 53887456200324134263052555)
        ·
          refine ⟨80831184300486201394578833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53887456200324134263052555 80831184300486201394578833)
          ·
            refine ⟨60623388225364651045934125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80831184300486201394578833 60623388225364651045934125)
            ·
              refine ⟨22733770584511744142225297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60623388225364651045934125 22733770584511744142225297)
              ·
                refine ⟨17050327938383808106668973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22733770584511744142225297 17050327938383808106668973)
                ·
                  refine ⟨6393872976893928040000865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17050327938383808106668973 6393872976893928040000865)
                  ·
                    refine ⟨4795404732670446030000649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6393872976893928040000865 4795404732670446030000649)
                    ·
                      refine ⟨3596553549502834522500487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795404732670446030000649 3596553549502834522500487)
                      ·
                        rfl

theorem cell23_7004263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_7004263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004263 prefixEnd_7004263 := by exact prefixLift 7004263
  have htrace : WordTrace (prefixWord ++ tailWord_7004263) baseStart_7004263 baseEnd_7004263 := by
    simpa [prefixWord, tailWord_7004263, baseEnd_7004263] using wordTrace_append hprefix tailTrace_7004263
  have hstable : (prefixWord ++ tailWord_7004263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004263).length < 2 ^ (prefixWord ++ tailWord_7004263).sum := by decide
  have hdescent : baseEnd_7004263 < baseStart_7004263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004339 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 3]
def baseStart_7004339 : Nat := 118140960795 + 7004339 * 2 ^ 59
def prefixEnd_7004339 : Nat := 4983230072969 + 3 ^ 40 * 7004339 * 2
def baseEnd_7004339 : Nat := 3596592574032576225150137

theorem tailTrace_7004339 : CollatzResearch.WordTrace tailWord_7004339 prefixEnd_7004339 3596592574032576225150137 := by
  unfold tailWord_7004339
  simp only [CollatzResearch.WordTrace]
  refine ⟨255469230971483523708312071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170312820647655682472208047 255469230971483523708312071)
  ·
    refine ⟨383203846457225285562468107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255469230971483523708312071 383203846457225285562468107)
    ·
      refine ⟨574805769685837928343702161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383203846457225285562468107 574805769685837928343702161)
      ·
        refine ⟨431104327264378446257776621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574805769685837928343702161 431104327264378446257776621)
        ·
          refine ⟨161664122724141917346666233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431104327264378446257776621 161664122724141917346666233)
          ·
            refine ⟨121248092043106438009999675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161664122724141917346666233 121248092043106438009999675)
            ·
              refine ⟨181872138064659657014999513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121248092043106438009999675 181872138064659657014999513)
              ·
                refine ⟨136404103548494742761249635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181872138064659657014999513 136404103548494742761249635)
                ·
                  refine ⟨204606155322742114141874453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136404103548494742761249635 204606155322742114141874453)
                  ·
                    refine ⟨9590913530753536600400365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 204606155322742114141874453 9590913530753536600400365)
                    ·
                      refine ⟨3596592574032576225150137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9590913530753536600400365 3596592574032576225150137)
                      ·
                        rfl

theorem cell23_7004339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_7004339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004339 prefixEnd_7004339 := by exact prefixLift 7004339
  have htrace : WordTrace (prefixWord ++ tailWord_7004339) baseStart_7004339 baseEnd_7004339 := by
    simpa [prefixWord, tailWord_7004339, baseEnd_7004339] using wordTrace_append hprefix tailTrace_7004339
  have hstable : (prefixWord ++ tailWord_7004339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004339).length < 2 ^ (prefixWord ++ tailWord_7004339).sum := by decide
  have hdescent : baseEnd_7004339 < baseStart_7004339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004364 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7004364 : Nat := 118140960795 + 7004364 * 2 ^ 59
def prefixEnd_7004364 : Nat := 4983230072969 + 3 ^ 40 * 7004364 * 2
def baseEnd_7004364 : Nat := 3596605411048938627337523

theorem tailTrace_7004364 : CollatzResearch.WordTrace tailWord_7004364 prefixEnd_7004364 3596605411048938627337523 := by
  unfold tailWord_7004364
  simp only [CollatzResearch.WordTrace]
  refine ⟨127735071398196476488986073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170313428530928635318648097 127735071398196476488986073)
  ·
    refine ⟨95801303548647357366739555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127735071398196476488986073 95801303548647357366739555)
    ·
      refine ⟨143701955322971036050109333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95801303548647357366739555 143701955322971036050109333)
      ·
        refine ⟨6736029155764267314848875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143701955322971036050109333 6736029155764267314848875)
        ·
          refine ⟨10104043733646400972273313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736029155764267314848875 10104043733646400972273313)
          ·
            refine ⟨7578032800234800729204985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10104043733646400972273313 7578032800234800729204985)
            ·
              refine ⟨5683524600176100546903739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7578032800234800729204985 5683524600176100546903739)
              ·
                refine ⟨8525286900264150820355609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683524600176100546903739 8525286900264150820355609)
                ·
                  refine ⟨6393965175198113115266707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8525286900264150820355609 6393965175198113115266707)
                  ·
                    refine ⟨9590947762797169672900061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6393965175198113115266707 9590947762797169672900061)
                    ·
                      refine ⟨3596605411048938627337523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9590947762797169672900061 3596605411048938627337523)
                      ·
                        rfl

theorem cell23_7004364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7004364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004364 prefixEnd_7004364 := by exact prefixLift 7004364
  have htrace : WordTrace (prefixWord ++ tailWord_7004364) baseStart_7004364 baseEnd_7004364 := by
    simpa [prefixWord, tailWord_7004364, baseEnd_7004364] using wordTrace_append hprefix tailTrace_7004364
  have hstable : (prefixWord ++ tailWord_7004364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004364).length < 2 ^ (prefixWord ++ tailWord_7004364).sum := by decide
  have hdescent : baseEnd_7004364 < baseStart_7004364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004374 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_7004374 : Nat := 118140960795 + 7004374 * 2 ^ 59
def prefixEnd_7004374 : Nat := 4983230072969 + 3 ^ 40 * 7004374 * 2
def baseEnd_7004374 : Nat := 3596610545855483588212477

theorem tailTrace_7004374 : CollatzResearch.WordTrace tailWord_7004374 prefixEnd_7004374 3596610545855483588212477 := by
  unfold tailWord_7004374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15966906720397295292864761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170313671684237816457224117 15966906720397295292864761)
  ·
    refine ⟨11975180040297971469648571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15966906720397295292864761 11975180040297971469648571)
    ·
      refine ⟨17962770060446957204472857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11975180040297971469648571 17962770060446957204472857)
      ·
        refine ⟨13472077545335217903354643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17962770060446957204472857 13472077545335217903354643)
        ·
          refine ⟨20208116318002826855031965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13472077545335217903354643 20208116318002826855031965)
          ·
            refine ⟨7578043619251060070636987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20208116318002826855031965 7578043619251060070636987)
            ·
              refine ⟨11367065428876590105955481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578043619251060070636987 11367065428876590105955481)
              ·
                refine ⟨8525299071657442579466611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11367065428876590105955481 8525299071657442579466611)
                ·
                  refine ⟨12787948607486163869199917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8525299071657442579466611 12787948607486163869199917)
                  ·
                    refine ⟨4795480727807311450949969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12787948607486163869199917 4795480727807311450949969)
                    ·
                      refine ⟨3596610545855483588212477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795480727807311450949969 3596610545855483588212477)
                      ·
                        rfl

theorem cell23_7004374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_7004374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004374 prefixEnd_7004374 := by exact prefixLift 7004374
  have htrace : WordTrace (prefixWord ++ tailWord_7004374) baseStart_7004374 baseEnd_7004374 := by
    simpa [prefixWord, tailWord_7004374, baseEnd_7004374] using wordTrace_append hprefix tailTrace_7004374
  have hstable : (prefixWord ++ tailWord_7004374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004374).length < 2 ^ (prefixWord ++ tailWord_7004374).sum := by decide
  have hdescent : baseEnd_7004374 < baseStart_7004374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004410 : List Nat := [3, 1, 1, 1, 1, 7, 2, 2, 5]
def baseStart_7004410 : Nat := 118140960795 + 7004410 * 2 ^ 59
def prefixEnd_7004410 : Nat := 4983230072969 + 3 ^ 40 * 7004410 * 2
def baseEnd_7004410 : Nat := 399625447906560605262479

theorem tailTrace_7004410 : CollatzResearch.WordTrace tailWord_7004410 prefixEnd_7004410 399625447906560605262479 := by
  unfold tailWord_7004410
  simp only [CollatzResearch.WordTrace]
  refine ⟨63867955138556575708536671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170314547036150868556097789 63867955138556575708536671)
  ·
    refine ⟨95801932707834863562805007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63867955138556575708536671 95801932707834863562805007)
    ·
      refine ⟨143702899061752295344207511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95801932707834863562805007 143702899061752295344207511)
      ·
        refine ⟨215554348592628443016311267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143702899061752295344207511 215554348592628443016311267)
        ·
          refine ⟨323331522888942664524466901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215554348592628443016311267 323331522888942664524466901)
          ·
            refine ⟨7578082567709593699792193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 323331522888942664524466901 7578082567709593699792193)
            ·
              refine ⟨5683561925782195274844145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7578082567709593699792193 5683561925782195274844145)
              ·
                refine ⟨4262671444336646456133109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5683561925782195274844145 4262671444336646456133109)
                ·
                  refine ⟨399625447906560605262479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4262671444336646456133109 399625447906560605262479)
                  ·
                    rfl

theorem cell23_7004410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_7004410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004410 prefixEnd_7004410 := by exact prefixLift 7004410
  have htrace : WordTrace (prefixWord ++ tailWord_7004410) baseStart_7004410 baseEnd_7004410 := by
    simpa [prefixWord, tailWord_7004410, baseEnd_7004410] using wordTrace_append hprefix tailTrace_7004410
  have hstable : (prefixWord ++ tailWord_7004410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004410).length < 2 ^ (prefixWord ++ tailWord_7004410).sum := by decide
  have hdescent : baseEnd_7004410 < baseStart_7004410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004426 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_7004426 : Nat := 118140960795 + 7004426 * 2 ^ 59
def prefixEnd_7004426 : Nat := 4983230072969 + 3 ^ 40 * 7004426 * 2
def baseEnd_7004426 : Nat := 3596637246849517384762237

theorem tailTrace_7004426 : CollatzResearch.WordTrace tailWord_7004426 prefixEnd_7004426 3596637246849517384762237 := by
  unfold tailWord_7004426
  simp only [CollatzResearch.WordTrace]
  refine ⟨63868101030542084391682283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170314936081445558377819421 63868101030542084391682283)
  ·
    refine ⟨95802151545813126587523425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63868101030542084391682283 95802151545813126587523425)
    ·
      refine ⟨71851613659359844940642569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95802151545813126587523425 71851613659359844940642569)
      ·
        refine ⟨53888710244519883705481927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71851613659359844940642569 53888710244519883705481927)
        ·
          refine ⟨80833065366779825558222891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53888710244519883705481927 80833065366779825558222891)
          ·
            refine ⟨121249598050169738337334337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80833065366779825558222891 121249598050169738337334337)
            ·
              refine ⟨90937198537627303753000753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121249598050169738337334337 90937198537627303753000753)
              ·
                refine ⟨68202898903220477814750565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90937198537627303753000753 68202898903220477814750565)
                ·
                  refine ⟨12788043544353839590265731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68202898903220477814750565 12788043544353839590265731)
                  ·
                    refine ⟨19182065316530759385398597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12788043544353839590265731 19182065316530759385398597)
                    ·
                      refine ⟨3596637246849517384762237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19182065316530759385398597 3596637246849517384762237)
                      ·
                        rfl

theorem cell23_7004426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_7004426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004426 prefixEnd_7004426 := by exact prefixLift 7004426
  have htrace : WordTrace (prefixWord ++ tailWord_7004426) baseStart_7004426 baseEnd_7004426 := by
    simpa [prefixWord, tailWord_7004426, baseEnd_7004426] using wordTrace_append hprefix tailTrace_7004426
  have hstable : (prefixWord ++ tailWord_7004426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004426).length < 2 ^ (prefixWord ++ tailWord_7004426).sum := by decide
  have hdescent : baseEnd_7004426 < baseStart_7004426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004503 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 1, 5, 2]
def baseStart_7004503 : Nat := 118140960795 + 7004503 * 2 ^ 59
def prefixEnd_7004503 : Nat := 4983230072969 + 3 ^ 40 * 7004503 * 2
def baseEnd_7004503 : Nat := 3596676784859913583499383

theorem tailTrace_7004503 : CollatzResearch.WordTrace tailWord_7004503 prefixEnd_7004503 3596676784859913583499383 := by
  unfold tailWord_7004503
  simp only [CollatzResearch.WordTrace]
  refine ⟨255475212542889379717282163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170316808361926253144854775 255475212542889379717282163)
  ·
    refine ⟨383212818814334069575923245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255475212542889379717282163 383212818814334069575923245)
    ·
      refine ⟨143704807055375276090971217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383212818814334069575923245 143704807055375276090971217)
      ·
        refine ⟨107778605291531457068228413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143704807055375276090971217 107778605291531457068228413)
        ·
          refine ⟨40416976984324296400585655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107778605291531457068228413 40416976984324296400585655)
          ·
            refine ⟨60625465476486444600878483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40416976984324296400585655 60625465476486444600878483)
            ·
              refine ⟨90938198214729666901317725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60625465476486444600878483 90938198214729666901317725)
              ·
                refine ⟨34101824330523625087994147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90938198214729666901317725 34101824330523625087994147)
                ·
                  refine ⟨51152736495785437631991221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34101824330523625087994147 51152736495785437631991221)
                  ·
                    refine ⟨4795569046479884777999177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51152736495785437631991221 4795569046479884777999177)
                    ·
                      refine ⟨3596676784859913583499383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795569046479884777999177 3596676784859913583499383)
                      ·
                        rfl

theorem cell23_7004503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_7004503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004503 prefixEnd_7004503 := by exact prefixLift 7004503
  have htrace : WordTrace (prefixWord ++ tailWord_7004503) baseStart_7004503 baseEnd_7004503 := by
    simpa [prefixWord, tailWord_7004503, baseEnd_7004503] using wordTrace_append hprefix tailTrace_7004503
  have hstable : (prefixWord ++ tailWord_7004503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004503).length < 2 ^ (prefixWord ++ tailWord_7004503).sum := by decide
  have hdescent : baseEnd_7004503 < baseStart_7004503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004520 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_7004520 : Nat := 118140960795 + 7004520 * 2 ^ 59
def prefixEnd_7004520 : Nat := 4983230072969 + 3 ^ 40 * 7004520 * 2
def baseEnd_7004520 : Nat := 3596685514031040016986805

theorem tailTrace_7004520 : CollatzResearch.WordTrace tailWord_7004520 prefixEnd_7004520 3596685514031040016986805 := by
  unfold tailWord_7004520
  simp only [CollatzResearch.WordTrace]
  refine ⟨127737916291913895810325507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170317221722551861080434009 127737916291913895810325507)
  ·
    refine ⟨191606874437870843715488261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127737916291913895810325507 191606874437870843715488261)
    ·
      refine ⟨35926288957100783196654049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191606874437870843715488261 35926288957100783196654049)
      ·
        refine ⟨26944716717825587397490537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35926288957100783196654049 26944716717825587397490537)
        ·
          refine ⟨20208537538369190548117903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26944716717825587397490537 20208537538369190548117903)
          ·
            refine ⟨30312806307553785822176855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20208537538369190548117903 30312806307553785822176855)
            ·
              refine ⟨45469209461330678733265283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30312806307553785822176855 45469209461330678733265283)
              ·
                refine ⟨68203814191996018099897925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45469209461330678733265283 68203814191996018099897925)
                ·
                  refine ⟨12788215160999253393730861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68203814191996018099897925 12788215160999253393730861)
                  ·
                    refine ⟨4795580685374720022649073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12788215160999253393730861 4795580685374720022649073)
                    ·
                      refine ⟨3596685514031040016986805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795580685374720022649073 3596685514031040016986805)
                      ·
                        rfl

theorem cell23_7004520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_7004520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004520 prefixEnd_7004520 := by exact prefixLift 7004520
  have htrace : WordTrace (prefixWord ++ tailWord_7004520) baseStart_7004520 baseEnd_7004520 := by
    simpa [prefixWord, tailWord_7004520, baseEnd_7004520] using wordTrace_append hprefix tailTrace_7004520
  have hstable : (prefixWord ++ tailWord_7004520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004520).length < 2 ^ (prefixWord ++ tailWord_7004520).sum := by decide
  have hdescent : baseEnd_7004520 < baseStart_7004520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004534 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_7004534 : Nat := 118140960795 + 7004534 * 2 ^ 59
def prefixEnd_7004534 : Nat := 4983230072969 + 3 ^ 40 * 7004534 * 2
def baseEnd_7004534 : Nat := 399632522528911440245749

theorem tailTrace_7004534 : CollatzResearch.WordTrace tailWord_7004534 prefixEnd_7004534 399632522528911440245749 := by
  unfold tailWord_7004534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15967271450361067000728791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170317562137184714674440437 15967271450361067000728791)
  ·
    refine ⟨23950907175541600501093187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15967271450361067000728791 23950907175541600501093187)
    ·
      refine ⟨35926360763312400751639781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23950907175541600501093187 35926360763312400751639781)
      ·
        refine ⟨6736192643121075140932459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35926360763312400751639781 6736192643121075140932459)
        ·
          refine ⟨10104288964681612711398689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736192643121075140932459 10104288964681612711398689)
          ·
            refine ⟨7578216723511209533549017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10104288964681612711398689 7578216723511209533549017)
            ·
              refine ⟨5683662542633407150161763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7578216723511209533549017 5683662542633407150161763)
              ·
                refine ⟨8525493813950110725242645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683662542633407150161763 8525493813950110725242645)
                ·
                  refine ⟨399632522528911440245749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8525493813950110725242645 399632522528911440245749)
                  ·
                    rfl

theorem cell23_7004534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_7004534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004534 prefixEnd_7004534 := by exact prefixLift 7004534
  have htrace : WordTrace (prefixWord ++ tailWord_7004534) baseStart_7004534 baseEnd_7004534 := by
    simpa [prefixWord, tailWord_7004534, baseEnd_7004534] using wordTrace_append hprefix tailTrace_7004534
  have hstable : (prefixWord ++ tailWord_7004534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004534).length < 2 ^ (prefixWord ++ tailWord_7004534).sum := by decide
  have hdescent : baseEnd_7004534 < baseStart_7004534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004543 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 2, 4]
def baseStart_7004543 : Nat := 118140960795 + 7004543 * 2 ^ 59
def prefixEnd_7004543 : Nat := 4983230072969 + 3 ^ 40 * 7004543 * 2
def baseEnd_7004543 : Nat := 1198899108028697808999733

theorem tailTrace_7004543 : CollatzResearch.WordTrace tailWord_7004543 prefixEnd_7004543 1198899108028697808999733 := by
  unfold tailWord_7004543
  simp only [CollatzResearch.WordTrace]
  refine ⟨255476671462744466548738283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170317780975162977699158855 255476671462744466548738283)
  ·
    refine ⟨383215007194116699823107425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255476671462744466548738283 383215007194116699823107425)
    ·
      refine ⟨287411255395587524867330569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383215007194116699823107425 287411255395587524867330569)
      ·
        refine ⟨215558441546690643650497927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287411255395587524867330569 215558441546690643650497927)
        ·
          refine ⟨323337662320035965475746891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215558441546690643650497927 323337662320035965475746891)
          ·
            refine ⟨485006493480053948213620337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323337662320035965475746891 485006493480053948213620337)
            ·
              refine ⟨363754870110040461160215253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485006493480053948213620337 363754870110040461160215253)
              ·
                refine ⟨8525504768204073308442545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 363754870110040461160215253 8525504768204073308442545)
                ·
                  refine ⟨6394128576153054981331909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8525504768204073308442545 6394128576153054981331909)
                  ·
                    refine ⟨1198899108028697808999733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6394128576153054981331909 1198899108028697808999733)
                    ·
                      rfl

theorem cell23_7004543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 4].length) (baseStart_7004543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004543 prefixEnd_7004543 := by exact prefixLift 7004543
  have htrace : WordTrace (prefixWord ++ tailWord_7004543) baseStart_7004543 baseEnd_7004543 := by
    simpa [prefixWord, tailWord_7004543, baseEnd_7004543] using wordTrace_append hprefix tailTrace_7004543
  have hstable : (prefixWord ++ tailWord_7004543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004543).length < 2 ^ (prefixWord ++ tailWord_7004543).sum := by decide
  have hdescent : baseEnd_7004543 < baseStart_7004543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004547 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 1, 5]
def baseStart_7004547 : Nat := 118140960795 + 7004547 * 2 ^ 59
def prefixEnd_7004547 : Nat := 4983230072969 + 3 ^ 40 * 7004547 * 2
def baseEnd_7004547 : Nat := 1198899792669570470449727

theorem tailTrace_7004547 : CollatzResearch.WordTrace tailWord_7004547 prefixEnd_7004547 1198899792669570470449727 := by
  unfold tailWord_7004547
  simp only [CollatzResearch.WordTrace]
  refine ⟨255476817354729975231883895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170317878236486650154589263 255476817354729975231883895)
  ·
    refine ⟨383215226032094962847825843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255476817354729975231883895 383215226032094962847825843)
    ·
      refine ⟨574822839048142444271738765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383215226032094962847825843 574822839048142444271738765)
      ·
        refine ⟨215558564643053416601902037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574822839048142444271738765 215558564643053416601902037)
        ·
          refine ⟨5052153858821564451607079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 215558564643053416601902037 5052153858821564451607079)
          ·
            refine ⟨7578230788232346677410619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5052153858821564451607079 7578230788232346677410619)
            ·
              refine ⟨11367346182348520016115929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578230788232346677410619 11367346182348520016115929)
              ·
                refine ⟨8525509636761390012086947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11367346182348520016115929 8525509636761390012086947)
                ·
                  refine ⟨12788264455142085018130421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8525509636761390012086947 12788264455142085018130421)
                  ·
                    refine ⟨1198899792669570470449727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12788264455142085018130421 1198899792669570470449727)
                    ·
                      rfl

theorem cell23_7004547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 5].length) (baseStart_7004547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004547 prefixEnd_7004547 := by exact prefixLift 7004547
  have htrace : WordTrace (prefixWord ++ tailWord_7004547) baseStart_7004547 baseEnd_7004547 := by
    simpa [prefixWord, tailWord_7004547, baseEnd_7004547] using wordTrace_append hprefix tailTrace_7004547
  have hstable : (prefixWord ++ tailWord_7004547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004547).length < 2 ^ (prefixWord ++ tailWord_7004547).sum := by decide
  have hdescent : baseEnd_7004547 < baseStart_7004547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004554 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7004554 : Nat := 118140960795 + 7004554 * 2 ^ 59
def prefixEnd_7004554 : Nat := 4983230072969 + 3 ^ 40 * 7004554 * 2
def baseEnd_7004554 : Nat := 3596702972373292883961649

theorem tailTrace_7004554 : CollatzResearch.WordTrace tailWord_7004554 prefixEnd_7004554 3596702972373292883961649 := by
  unfold tailWord_7004554
  simp only [CollatzResearch.WordTrace]
  refine ⟨63869268166426153856847179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170318048443803076951592477 63869268166426153856847179)
  ·
    refine ⟨95803902249639230785270769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63869268166426153856847179 95803902249639230785270769)
    ·
      refine ⟨71852926687229423088953077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95803902249639230785270769 71852926687229423088953077)
      ·
        refine ⟨6736211876927758414589351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71852926687229423088953077 6736211876927758414589351)
        ·
          refine ⟨10104317815391637621884027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736211876927758414589351 10104317815391637621884027)
          ·
            refine ⟨15156476723087456432826041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104317815391637621884027 15156476723087456432826041)
            ·
              refine ⟨11367357542315592324619531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15156476723087456432826041 11367357542315592324619531)
              ·
                refine ⟨17051036313473388486929297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11367357542315592324619531 17051036313473388486929297)
                ·
                  refine ⟨12788277235105041365196973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17051036313473388486929297 12788277235105041365196973)
                  ·
                    refine ⟨4795603963164390511948865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12788277235105041365196973 4795603963164390511948865)
                    ·
                      refine ⟨3596702972373292883961649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795603963164390511948865 3596702972373292883961649)
                      ·
                        rfl

theorem cell23_7004554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7004554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004554 prefixEnd_7004554 := by exact prefixLift 7004554
  have htrace : WordTrace (prefixWord ++ tailWord_7004554) baseStart_7004554 baseEnd_7004554 := by
    simpa [prefixWord, tailWord_7004554, baseEnd_7004554] using wordTrace_append hprefix tailTrace_7004554
  have hstable : (prefixWord ++ tailWord_7004554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004554).length < 2 ^ (prefixWord ++ tailWord_7004554).sum := by decide
  have hdescent : baseEnd_7004554 < baseStart_7004554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004556 : List Nat := [2, 2, 1, 2, 1, 4, 2, 9]
def baseStart_7004556 : Nat := 118140960795 + 7004556 * 2 ^ 59
def prefixEnd_7004556 : Nat := 4983230072969 + 3 ^ 40 * 7004556 * 2
def baseEnd_7004556 : Nat := 133211259234614884301357

theorem tailTrace_7004556 : CollatzResearch.WordTrace tailWord_7004556 prefixEnd_7004556 133211259234614884301357 := by
  unfold tailWord_7004556
  simp only [CollatzResearch.WordTrace]
  refine ⟨127738572805848684884480761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170318097074464913179307681 127738572805848684884480761)
  ·
    refine ⟨95803929604386513663360571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127738572805848684884480761 95803929604386513663360571)
    ·
      refine ⟨143705894406579770495040857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95803929604386513663360571 143705894406579770495040857)
      ·
        refine ⟨107779420804934827871280643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143705894406579770495040857 107779420804934827871280643)
        ·
          refine ⟨161669131207402241806920965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107779420804934827871280643 161669131207402241806920965)
          ·
            refine ⟨30312962101387920338797681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161669131207402241806920965 30312962101387920338797681)
            ·
              refine ⟨22734721576040940254098261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30312962101387920338797681 22734721576040940254098261)
              ·
                refine ⟨133211259234614884301357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22734721576040940254098261 133211259234614884301357)
                ·
                  rfl

theorem cell23_7004556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 9].length) (baseStart_7004556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004556 prefixEnd_7004556 := by exact prefixLift 7004556
  have htrace : WordTrace (prefixWord ++ tailWord_7004556) baseStart_7004556 baseEnd_7004556 := by
    simpa [prefixWord, tailWord_7004556, baseEnd_7004556] using wordTrace_append hprefix tailTrace_7004556
  have hstable : (prefixWord ++ tailWord_7004556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004556).length < 2 ^ (prefixWord ++ tailWord_7004556).sum := by decide
  have hdescent : baseEnd_7004556 < baseStart_7004556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004570 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5]
def baseStart_7004570 : Nat := 118140960795 + 7004570 * 2 ^ 59
def prefixEnd_7004570 : Nat := 4983230072969 + 3 ^ 40 * 7004570 * 2
def baseEnd_7004570 : Nat := 3596711188063764821361575

theorem tailTrace_7004570 : CollatzResearch.WordTrace tailWord_7004570 prefixEnd_7004570 3596711188063764821361575 := by
  unfold tailWord_7004570
  simp only [CollatzResearch.WordTrace]
  refine ⟨63869414058411662539992791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170318437489097766773314109 63869414058411662539992791)
  ·
    refine ⟨95804121087617493809989187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63869414058411662539992791 95804121087617493809989187)
    ·
      refine ⟨143706181631426240714983781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95804121087617493809989187 143706181631426240714983781)
      ·
        refine ⟨26944909055892420134059459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143706181631426240714983781 26944909055892420134059459)
        ·
          refine ⟨40417363583838630201089189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26944909055892420134059459 40417363583838630201089189)
          ·
            refine ⟨7578255671969743162704223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40417363583838630201089189 7578255671969743162704223)
            ·
              refine ⟨11367383507954614744056335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578255671969743162704223 11367383507954614744056335)
              ·
                refine ⟨17051075261931922116084503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11367383507954614744056335 17051075261931922116084503)
                ·
                  refine ⟨25576612892897883174126755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17051075261931922116084503 25576612892897883174126755)
                  ·
                    refine ⟨38364919339346824761190133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25576612892897883174126755 38364919339346824761190133)
                    ·
                      refine ⟨3596711188063764821361575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38364919339346824761190133 3596711188063764821361575)
                      ·
                        rfl

theorem cell23_7004570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_7004570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004570 prefixEnd_7004570 := by exact prefixLift 7004570
  have htrace : WordTrace (prefixWord ++ tailWord_7004570) baseStart_7004570 baseEnd_7004570 := by
    simpa [prefixWord, tailWord_7004570, baseEnd_7004570] using wordTrace_append hprefix tailTrace_7004570
  have hstable : (prefixWord ++ tailWord_7004570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004570).length < 2 ^ (prefixWord ++ tailWord_7004570).sum := by decide
  have hdescent : baseEnd_7004570 < baseStart_7004570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004573 : List Nat := [1, 4, 2, 1, 5, 10]
def baseStart_7004573 : Nat := 118140960795 + 7004573 * 2 ^ 59
def prefixEnd_7004573 : Nat := 4983230072969 + 3 ^ 40 * 7004573 * 2
def baseEnd_7004573 : Nat := 14801286948583244072527

theorem tailTrace_7004573 : CollatzResearch.WordTrace tailWord_7004573 prefixEnd_7004573 14801286948583244072527 := by
  unfold tailWord_7004573
  simp only [CollatzResearch.WordTrace]
  refine ⟨255477765652635781672330373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170318510435090521114886915 255477765652635781672330373)
  ·
    refine ⟨47902081059869209063561945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255477765652635781672330373 47902081059869209063561945)
    ·
      refine ⟨35926560794901906797671459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47902081059869209063561945 35926560794901906797671459)
      ·
        refine ⟨53889841192352860196507189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35926560794901906797671459 53889841192352860196507189)
        ·
          refine ⟨5052172611783080643422549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53889841192352860196507189 5052172611783080643422549)
          ·
            refine ⟨14801286948583244072527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5052172611783080643422549 14801286948583244072527)
            ·
              rfl

theorem cell23_7004573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 10].length) (baseStart_7004573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004573 prefixEnd_7004573 := by exact prefixLift 7004573
  have htrace : WordTrace (prefixWord ++ tailWord_7004573) baseStart_7004573 baseEnd_7004573 := by
    simpa [prefixWord, tailWord_7004573, baseEnd_7004573] using wordTrace_append hprefix tailTrace_7004573
  have hstable : (prefixWord ++ tailWord_7004573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004573).length < 2 ^ (prefixWord ++ tailWord_7004573).sum := by decide
  have hdescent : baseEnd_7004573 < baseStart_7004573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004661 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7004661 : Nat := 118140960795 + 7004661 * 2 ^ 59
def prefixEnd_7004661 : Nat := 4983230072969 + 3 ^ 40 * 7004661 * 2
def baseEnd_7004661 : Nat := 3596757914803323965323657

theorem tailTrace_7004661 : CollatzResearch.WordTrace tailWord_7004661 prefixEnd_7004661 3596757914803323965323657 := by
  unfold tailWord_7004661
  simp only [CollatzResearch.WordTrace]
  refine ⟨255480975276316972701533837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170320650184211315134355891 255480975276316972701533837)
  ·
    refine ⟨95805365728618864763075189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255480975276316972701533837 95805365728618864763075189)
    ·
      refine ⟨8981753037058018571538299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95805365728618864763075189 8981753037058018571538299)
      ·
        refine ⟨13472629555587027857307449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8981753037058018571538299 13472629555587027857307449)
        ·
          refine ⟨10104472166690270892980587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13472629555587027857307449 10104472166690270892980587)
          ·
            refine ⟨15156708250035406339470881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104472166690270892980587 15156708250035406339470881)
            ·
              refine ⟨11367531187526554754603161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15156708250035406339470881 11367531187526554754603161)
              ·
                refine ⟨8525648390644916065952371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11367531187526554754603161 8525648390644916065952371)
                ·
                  refine ⟨12788472585967374098928557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8525648390644916065952371 12788472585967374098928557)
                  ·
                    refine ⟨4795677219737765287098209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12788472585967374098928557 4795677219737765287098209)
                    ·
                      refine ⟨3596757914803323965323657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795677219737765287098209 3596757914803323965323657)
                      ·
                        rfl

theorem cell23_7004661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7004661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004661 prefixEnd_7004661 := by exact prefixLift 7004661
  have htrace : WordTrace (prefixWord ++ tailWord_7004661) baseStart_7004661 baseEnd_7004661 := by
    simpa [prefixWord, tailWord_7004661, baseEnd_7004661] using wordTrace_append hprefix tailTrace_7004661
  have hstable : (prefixWord ++ tailWord_7004661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004661).length < 2 ^ (prefixWord ++ tailWord_7004661).sum := by decide
  have hdescent : baseEnd_7004661 < baseStart_7004661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004678 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_7004678 : Nat := 118140960795 + 7004678 * 2 ^ 59
def prefixEnd_7004678 : Nat := 4983230072969 + 3 ^ 40 * 7004678 * 2
def baseEnd_7004678 : Nat := 3596766643974450398811079

theorem tailTrace_7004678 : CollatzResearch.WordTrace tailWord_7004678 prefixEnd_7004678 3596766643974450398811079 := by
  unfold tailWord_7004678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7983799853664230768903209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170321063544836923069935125 7983799853664230768903209)
  ·
    refine ⟨5987849890248173076677407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7983799853664230768903209 5987849890248173076677407)
    ·
      refine ⟨8981774835372259615016111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5987849890248173076677407 8981774835372259615016111)
      ·
        refine ⟨13472662253058389422524167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8981774835372259615016111 13472662253058389422524167)
        ·
          refine ⟨20208993379587584133786251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13472662253058389422524167 20208993379587584133786251)
          ·
            refine ⟨30313490069381376200679377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20208993379587584133786251 30313490069381376200679377)
            ·
              refine ⟨22735117552036032150509533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30313490069381376200679377 22735117552036032150509533)
              ·
                refine ⟨8525669082013512056441075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22735117552036032150509533 8525669082013512056441075)
                ·
                  refine ⟨12788503623020268084661613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8525669082013512056441075 12788503623020268084661613)
                  ·
                    refine ⟨4795688858632600531748105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12788503623020268084661613 4795688858632600531748105)
                    ·
                      refine ⟨3596766643974450398811079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795688858632600531748105 3596766643974450398811079)
                      ·
                        rfl

theorem cell23_7004678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_7004678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004678 prefixEnd_7004678 := by exact prefixLift 7004678
  have htrace : WordTrace (prefixWord ++ tailWord_7004678) baseStart_7004678 baseEnd_7004678 := by
    simpa [prefixWord, tailWord_7004678, baseEnd_7004678] using wordTrace_append hprefix tailTrace_7004678
  have hstable : (prefixWord ++ tailWord_7004678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004678).length < 2 ^ (prefixWord ++ tailWord_7004678).sum := by decide
  have hdescent : baseEnd_7004678 < baseStart_7004678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004730 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_7004730 : Nat := 118140960795 + 7004730 * 2 ^ 59
def prefixEnd_7004730 : Nat := 4983230072969 + 3 ^ 40 * 7004730 * 2
def baseEnd_7004730 : Nat := 3596793344968484195360839

theorem tailTrace_7004730 : CollatzResearch.WordTrace tailWord_7004730 prefixEnd_7004730 3596793344968484195360839 := by
  unfold tailWord_7004730
  simp only [CollatzResearch.WordTrace]
  refine ⟨63870872978266749371448911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170322327942044664990530429 63870872978266749371448911)
  ·
    refine ⟨95806309467400124057173367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63870872978266749371448911 95806309467400124057173367)
    ·
      refine ⟨143709464201100186085760051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95806309467400124057173367 143709464201100186085760051)
      ·
        refine ⟨215564196301650279128640077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143709464201100186085760051 215564196301650279128640077)
        ·
          refine ⟨80836573613118854673240029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215564196301650279128640077 80836573613118854673240029)
          ·
            refine ⟨30313715104919570502465011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80836573613118854673240029 30313715104919570502465011)
            ·
              refine ⟨45470572657379355753697517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30313715104919570502465011 45470572657379355753697517)
              ·
                refine ⟨17051464746517258407636569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45470572657379355753697517 17051464746517258407636569)
                ·
                  refine ⟨12788598559887943805727427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17051464746517258407636569 12788598559887943805727427)
                  ·
                    refine ⟨19182897839831915708591141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12788598559887943805727427 19182897839831915708591141)
                    ·
                      refine ⟨3596793344968484195360839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19182897839831915708591141 3596793344968484195360839)
                      ·
                        rfl

theorem cell23_7004730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_7004730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004730 prefixEnd_7004730 := by exact prefixLift 7004730
  have htrace : WordTrace (prefixWord ++ tailWord_7004730) baseStart_7004730 baseEnd_7004730 := by
    simpa [prefixWord, tailWord_7004730, baseEnd_7004730] using wordTrace_append hprefix tailTrace_7004730
  have hstable : (prefixWord ++ tailWord_7004730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004730).length < 2 ^ (prefixWord ++ tailWord_7004730).sum := by decide
  have hdescent : baseEnd_7004730 < baseStart_7004730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004764 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_7004764 : Nat := 118140960795 + 7004764 * 2 ^ 59
def prefixEnd_7004764 : Nat := 4983230072969 + 3 ^ 40 * 7004764 * 2
def baseEnd_7004764 : Nat := 3596810803310737062335683

theorem tailTrace_7004764 : CollatzResearch.WordTrace tailWord_7004764 prefixEnd_7004764 3596810803310737062335683 := by
  unfold tailWord_7004764
  simp only [CollatzResearch.WordTrace]
  refine ⟨127742365997471910646266673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170323154663295880861688897 127742365997471910646266673)
  ·
    refine ⟨95806774498103932984700005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127742365997471910646266673 95806774498103932984700005)
    ·
      refine ⟨17963770218394487434631251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95806774498103932984700005 17963770218394487434631251)
      ·
        refine ⟨26945655327591731151946877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17963770218394487434631251 26945655327591731151946877)
        ·
          refine ⟨10104620747846899181980079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26945655327591731151946877 10104620747846899181980079)
          ·
            refine ⟨15156931121770348772970119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104620747846899181980079 15156931121770348772970119)
            ·
              refine ⟨22735396682655523159455179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15156931121770348772970119 22735396682655523159455179)
              ·
                refine ⟨34103095023983284739182769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22735396682655523159455179 34103095023983284739182769)
                ·
                  refine ⟨25577321267987463554387077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34103095023983284739182769 25577321267987463554387077)
                  ·
                    refine ⟨4795747737747649416447577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25577321267987463554387077 4795747737747649416447577)
                    ·
                      refine ⟨3596810803310737062335683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795747737747649416447577 3596810803310737062335683)
                      ·
                        rfl

theorem cell23_7004764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_7004764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004764 prefixEnd_7004764 := by exact prefixLift 7004764
  have htrace : WordTrace (prefixWord ++ tailWord_7004764) baseStart_7004764 baseEnd_7004764 := by
    simpa [prefixWord, tailWord_7004764, baseEnd_7004764] using wordTrace_append hprefix tailTrace_7004764
  have hstable : (prefixWord ++ tailWord_7004764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004764).length < 2 ^ (prefixWord ++ tailWord_7004764).sum := by decide
  have hdescent : baseEnd_7004764 < baseStart_7004764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004784 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 3]
def baseStart_7004784 : Nat := 118140960795 + 7004784 * 2 ^ 59
def prefixEnd_7004784 : Nat := 4983230072969 + 3 ^ 40 * 7004784 * 2
def baseEnd_7004784 : Nat := 3596821072923826984085591

theorem tailTrace_7004784 : CollatzResearch.WordTrace tailWord_7004784 prefixEnd_7004784 3596821072923826984085591 := by
  unfold tailWord_7004784
  simp only [CollatzResearch.WordTrace]
  refine ⟨127742730727435682354130703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170323640969914243138840937 127742730727435682354130703)
  ·
    refine ⟨191614096091153523531196055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127742730727435682354130703 191614096091153523531196055)
    ·
      refine ⟨287421144136730285296794083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191614096091153523531196055 287421144136730285296794083)
      ·
        refine ⟨431131716205095427945191125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287421144136730285296794083 431131716205095427945191125)
        ·
          refine ⟨10104649598556924092465417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 431131716205095427945191125 10104649598556924092465417)
          ·
            refine ⟨7578487198917693069349063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10104649598556924092465417 7578487198917693069349063)
            ·
              refine ⟨11367730798376539604023595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578487198917693069349063 11367730798376539604023595)
              ·
                refine ⟨17051596197564809406035393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11367730798376539604023595 17051596197564809406035393)
                ·
                  refine ⟨12788697148173607054526545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17051596197564809406035393 12788697148173607054526545)
                  ·
                    refine ⟨9591522861130205290894909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12788697148173607054526545 9591522861130205290894909)
                    ·
                      refine ⟨3596821072923826984085591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9591522861130205290894909 3596821072923826984085591)
                      ·
                        rfl

theorem cell23_7004784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 3].length) (baseStart_7004784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004784 prefixEnd_7004784 := by exact prefixLift 7004784
  have htrace : WordTrace (prefixWord ++ tailWord_7004784) baseStart_7004784 baseEnd_7004784 := by
    simpa [prefixWord, tailWord_7004784, baseEnd_7004784] using wordTrace_append hprefix tailTrace_7004784
  have hstable : (prefixWord ++ tailWord_7004784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004784).length < 2 ^ (prefixWord ++ tailWord_7004784).sum := by decide
  have hdescent : baseEnd_7004784 < baseStart_7004784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004807 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_7004807 : Nat := 118140960795 + 7004807 * 2 ^ 59
def prefixEnd_7004807 : Nat := 4983230072969 + 3 ^ 40 * 7004807 * 2
def baseEnd_7004807 : Nat := 3596832882978880394097985

theorem tailTrace_7004807 : CollatzResearch.WordTrace tailWord_7004807 prefixEnd_7004807 3596832882978880394097985 := by
  unfold tailWord_7004807
  simp only [CollatzResearch.WordTrace]
  refine ⟨255486300333788039636348675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170324200222525359757565783 255486300333788039636348675)
  ·
    refine ⟨383229450500682059454523013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255486300333788039636348675 383229450500682059454523013)
    ·
      refine ⟨71855521968877886147723065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383229450500682059454523013 71855521968877886147723065)
      ·
        refine ⟨53891641476658414610792299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71855521968877886147723065 53891641476658414610792299)
        ·
          refine ⟨80837462214987621916188449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53891641476658414610792299 80837462214987621916188449)
          ·
            refine ⟨60628096661240716437141337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80837462214987621916188449 60628096661240716437141337)
            ·
              refine ⟨45471072495930537327856003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60628096661240716437141337 45471072495930537327856003)
              ·
                refine ⟨68206608743895805991784005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45471072495930537327856003 68206608743895805991784005)
                ·
                  refine ⟨12788739139480463623459501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68206608743895805991784005 12788739139480463623459501)
                  ·
                    refine ⟨4795777177305173858797313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12788739139480463623459501 4795777177305173858797313)
                    ·
                      refine ⟨3596832882978880394097985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795777177305173858797313 3596832882978880394097985)
                      ·
                        rfl

theorem cell23_7004807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_7004807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004807 prefixEnd_7004807 := by exact prefixLift 7004807
  have htrace : WordTrace (prefixWord ++ tailWord_7004807) baseStart_7004807 baseEnd_7004807 := by
    simpa [prefixWord, tailWord_7004807, baseEnd_7004807] using wordTrace_append hprefix tailTrace_7004807
  have hstable : (prefixWord ++ tailWord_7004807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004807).length < 2 ^ (prefixWord ++ tailWord_7004807).sum := by decide
  have hdescent : baseEnd_7004807 < baseStart_7004807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004814 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_7004814 : Nat := 118140960795 + 7004814 * 2 ^ 59
def prefixEnd_7004814 : Nat := 4983230072969 + 3 ^ 40 * 7004814 * 2
def baseEnd_7004814 : Nat := 3596836477343461866710453

theorem tailTrace_7004814 : CollatzResearch.WordTrace tailWord_7004814 prefixEnd_7004814 3596836477343461866710453 := by
  unfold tailWord_7004814
  simp only [CollatzResearch.WordTrace]
  refine ⟨31935819455595334978981687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170324370429841786554568997 31935819455595334978981687)
  ·
    refine ⟨47903729183393002468472531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31935819455595334978981687 47903729183393002468472531)
    ·
      refine ⟨71855593775089503702708797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47903729183393002468472531 71855593775089503702708797)
      ·
        refine ⟨26945847665658563888515799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71855593775089503702708797 26945847665658563888515799)
        ·
          refine ⟨40418771498487845832773699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26945847665658563888515799 40418771498487845832773699)
          ·
            refine ⟨60628157247731768749160549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40418771498487845832773699 60628157247731768749160549)
            ·
              refine ⟨11367779483949706640467603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60628157247731768749160549 11367779483949706640467603)
              ·
                refine ⟨17051669225924559960701405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11367779483949706640467603 17051669225924559960701405)
                ·
                  refine ⟨6394375959721709985263027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17051669225924559960701405 6394375959721709985263027)
                  ·
                    refine ⟨9591563939582564977894541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6394375959721709985263027 9591563939582564977894541)
                    ·
                      refine ⟨3596836477343461866710453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9591563939582564977894541 3596836477343461866710453)
                      ·
                        rfl

theorem cell23_7004814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_7004814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004814 prefixEnd_7004814 := by exact prefixLift 7004814
  have htrace : WordTrace (prefixWord ++ tailWord_7004814) baseStart_7004814 baseEnd_7004814 := by
    simpa [prefixWord, tailWord_7004814, baseEnd_7004814] using wordTrace_append hprefix tailTrace_7004814
  have hstable : (prefixWord ++ tailWord_7004814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004814).length < 2 ^ (prefixWord ++ tailWord_7004814).sum := by decide
  have hdescent : baseEnd_7004814 < baseStart_7004814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004850 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_7004850 : Nat := 118140960795 + 7004850 * 2 ^ 59
def prefixEnd_7004850 : Nat := 4983230072969 + 3 ^ 40 * 7004850 * 2
def baseEnd_7004850 : Nat := 3596854962647023725860287

theorem tailTrace_7004850 : CollatzResearch.WordTrace tailWord_7004850 prefixEnd_7004850 3596854962647023725860287 := by
  unfold tailWord_7004850
  simp only [CollatzResearch.WordTrace]
  refine ⟨63871967168158064495041001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170325245781754838653442669 63871967168158064495041001)
  ·
    refine ⟨47903975376118548371280751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63871967168158064495041001 47903975376118548371280751)
    ·
      refine ⟨71855963064177822556921127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47903975376118548371280751 71855963064177822556921127)
      ·
        refine ⟨107783944596266733835381691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71855963064177822556921127 107783944596266733835381691)
        ·
          refine ⟨161675916894400100753072537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107783944596266733835381691 161675916894400100753072537)
          ·
            refine ⟨121256937670800075564804403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161675916894400100753072537 121256937670800075564804403)
            ·
              refine ⟨181885406506200113347206605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121256937670800075564804403 181885406506200113347206605)
              ·
                refine ⟨68207027439825042505202477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181885406506200113347206605 68207027439825042505202477)
                ·
                  refine ⟨25577635289934390939450929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68207027439825042505202477 25577635289934390939450929)
                  ·
                    refine ⟨19183226467450793204588197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25577635289934390939450929 19183226467450793204588197)
                    ·
                      refine ⟨3596854962647023725860287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19183226467450793204588197 3596854962647023725860287)
                      ·
                        rfl

theorem cell23_7004850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_7004850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004850 prefixEnd_7004850 := by exact prefixLift 7004850
  have htrace : WordTrace (prefixWord ++ tailWord_7004850) baseStart_7004850 baseEnd_7004850 := by
    simpa [prefixWord, tailWord_7004850, baseEnd_7004850] using wordTrace_append hprefix tailTrace_7004850
  have hstable : (prefixWord ++ tailWord_7004850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004850).length < 2 ^ (prefixWord ++ tailWord_7004850).sum := by decide
  have hdescent : baseEnd_7004850 < baseStart_7004850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004865 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7004865 : Nat := 118140960795 + 7004865 * 2 ^ 59
def prefixEnd_7004865 : Nat := 4983230072969 + 3 ^ 40 * 7004865 * 2
def baseEnd_7004865 : Nat := 3596862664856841167172719

theorem tailTrace_7004865 : CollatzResearch.WordTrace tailWord_7004865 prefixEnd_7004865 3596862664856841167172719 := by
  unfold tailWord_7004865
  simp only [CollatzResearch.WordTrace]
  refine ⟨255488415767577915541960049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170325610511718610361306699 255488415767577915541960049)
  ·
    refine ⟨191616311825683436656470037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255488415767577915541960049 191616311825683436656470037)
    ·
      refine ⟨8982014616828911093272033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 191616311825683436656470037 8982014616828911093272033)
      ·
        refine ⟨6736510962621683319954025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8982014616828911093272033 6736510962621683319954025)
        ·
          refine ⟨5052383221966262489965519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6736510962621683319954025 5052383221966262489965519)
          ·
            refine ⟨7578574832949393734948279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5052383221966262489965519 7578574832949393734948279)
            ·
              refine ⟨11367862249424090602422419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578574832949393734948279 11367862249424090602422419)
              ·
                refine ⟨17051793374136135903633629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11367862249424090602422419 17051793374136135903633629)
                ·
                  refine ⟨6394422515301050963862611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17051793374136135903633629 6394422515301050963862611)
                  ·
                    refine ⟨9591633772951576445793917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6394422515301050963862611 9591633772951576445793917)
                    ·
                      refine ⟨3596862664856841167172719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9591633772951576445793917 3596862664856841167172719)
                      ·
                        rfl

theorem cell23_7004865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7004865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004865 prefixEnd_7004865 := by exact prefixLift 7004865
  have htrace : WordTrace (prefixWord ++ tailWord_7004865) baseStart_7004865 baseEnd_7004865 := by
    simpa [prefixWord, tailWord_7004865, baseEnd_7004865] using wordTrace_append hprefix tailTrace_7004865
  have hstable : (prefixWord ++ tailWord_7004865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004865).length < 2 ^ (prefixWord ++ tailWord_7004865).sum := by decide
  have hdescent : baseEnd_7004865 < baseStart_7004865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004904 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_7004904 : Nat := 118140960795 + 7004904 * 2 ^ 59
def prefixEnd_7004904 : Nat := 4983230072969 + 3 ^ 40 * 7004904 * 2
def baseEnd_7004904 : Nat := 3596882690602366514585039

theorem tailTrace_7004904 : CollatzResearch.WordTrace tailWord_7004904 prefixEnd_7004904 3596882690602366514585039 := by
  unfold tailWord_7004904
  simp only [CollatzResearch.WordTrace]
  refine ⟨127744919107218312601314883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170326558809624416801753177 127744919107218312601314883)
  ·
    refine ⟨191617378660827468901972325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127744919107218312601314883 191617378660827468901972325)
    ·
      refine ⟨35928258498905150419119811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191617378660827468901972325 35928258498905150419119811)
      ·
        refine ⟨53892387748357725628679717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35928258498905150419119811 53892387748357725628679717)
        ·
          refine ⟨10104822702817073555377447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53892387748357725628679717 10104822702817073555377447)
          ·
            refine ⟨15157234054225610333066171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104822702817073555377447 15157234054225610333066171)
            ·
              refine ⟨22735851081338415499599257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15157234054225610333066171 22735851081338415499599257)
              ·
                refine ⟨17051888311003811624699443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22735851081338415499599257 17051888311003811624699443)
                ·
                  refine ⟨25577832466505717437049165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17051888311003811624699443 25577832466505717437049165)
                  ·
                    refine ⟨9591687174939644038893437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25577832466505717437049165 9591687174939644038893437)
                    ·
                      refine ⟨3596882690602366514585039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9591687174939644038893437 3596882690602366514585039)
                      ·
                        rfl

theorem cell23_7004904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_7004904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004904 prefixEnd_7004904 := by exact prefixLift 7004904
  have htrace : WordTrace (prefixWord ++ tailWord_7004904) baseStart_7004904 baseEnd_7004904 := by
    simpa [prefixWord, tailWord_7004904, baseEnd_7004904] using wordTrace_append hprefix tailTrace_7004904
  have hstable : (prefixWord ++ tailWord_7004904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004904).length < 2 ^ (prefixWord ++ tailWord_7004904).sum := by decide
  have hdescent : baseEnd_7004904 < baseStart_7004904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004920 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 2, 6]
def baseStart_7004920 : Nat := 118140960795 + 7004920 * 2 ^ 59
def prefixEnd_7004920 : Nat := 4983230072969 + 3 ^ 40 * 7004920 * 2
def baseEnd_7004920 : Nat := 1198963635430946150661655

theorem tailTrace_7004920 : CollatzResearch.WordTrace tailWord_7004920 prefixEnd_7004920 1198963635430946150661655 := by
  unfold tailWord_7004920
  simp only [CollatzResearch.WordTrace]
  refine ⟨127745210891189329967606107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170326947854919106623474809 127745210891189329967606107)
  ·
    refine ⟨191617816336783994951409161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127745210891189329967606107 191617816336783994951409161)
    ·
      refine ⟨143713362252587996213556871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191617816336783994951409161 143713362252587996213556871)
      ·
        refine ⟨215570043378881994320335307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143713362252587996213556871 215570043378881994320335307)
        ·
          refine ⟨323355065068322991480502961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215570043378881994320335307 323355065068322991480502961)
          ·
            refine ⟨242516298801242243610377221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323355065068322991480502961 242516298801242243610377221)
            ·
              refine ⟨45471806025232920676945729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242516298801242243610377221 45471806025232920676945729)
              ·
                refine ⟨34103854518924690507709297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45471806025232920676945729 34103854518924690507709297)
                ·
                  refine ⟨25577890889193517880781973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34103854518924690507709297 25577890889193517880781973)
                  ·
                    refine ⟨1198963635430946150661655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25577890889193517880781973 1198963635430946150661655)
                    ·
                      rfl

theorem cell23_7004920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_7004920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004920 prefixEnd_7004920 := by exact prefixLift 7004920
  have htrace : WordTrace (prefixWord ++ tailWord_7004920) baseStart_7004920 baseEnd_7004920 := by
    simpa [prefixWord, tailWord_7004920, baseEnd_7004920] using wordTrace_append hprefix tailTrace_7004920
  have hstable : (prefixWord ++ tailWord_7004920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004920).length < 2 ^ (prefixWord ++ tailWord_7004920).sum := by decide
  have hdescent : baseEnd_7004920 < baseStart_7004920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004927 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 5, 4, 2]
def baseStart_7004927 : Nat := 118140960795 + 7004927 * 2 ^ 59
def prefixEnd_7004927 : Nat := 4983230072969 + 3 ^ 40 * 7004927 * 2
def baseEnd_7004927 : Nat := 3596894500657419924597433

theorem tailTrace_7004927 : CollatzResearch.WordTrace tailWord_7004927 prefixEnd_7004927 3596894500657419924597433 := by
  unfold tailWord_7004927
  simp only [CollatzResearch.WordTrace]
  refine ⟨255490677093353300130717035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170327118062235533420478023 255490677093353300130717035)
  ·
    refine ⟨383236015640029950196075553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255490677093353300130717035 383236015640029950196075553)
    ·
      refine ⟨287427011730022462647056665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383236015640029950196075553 287427011730022462647056665)
      ·
        refine ⟨215570258797516846985292499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287427011730022462647056665 215570258797516846985292499)
        ·
          refine ⟨323355388196275270477938749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215570258797516846985292499 323355388196275270477938749)
          ·
            refine ⟨121258270573603226429227031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323355388196275270477938749 121258270573603226429227031)
            ·
              refine ⟨181887405860404839643840547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121258270573603226429227031 181887405860404839643840547)
              ·
                refine ⟨272831108790607259465760821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181887405860404839643840547 272831108790607259465760821)
                ·
                  refine ⟨25577916449119430574915077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272831108790607259465760821 25577916449119430574915077)
                  ·
                    refine ⟨4795859334209893232796577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25577916449119430574915077 4795859334209893232796577)
                    ·
                      refine ⟨3596894500657419924597433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4795859334209893232796577 3596894500657419924597433)
                      ·
                        rfl

theorem cell23_7004927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_7004927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004927 prefixEnd_7004927 := by exact prefixLift 7004927
  have htrace : WordTrace (prefixWord ++ tailWord_7004927) baseStart_7004927 baseEnd_7004927 := by
    simpa [prefixWord, tailWord_7004927, baseEnd_7004927] using wordTrace_append hprefix tailTrace_7004927
  have hstable : (prefixWord ++ tailWord_7004927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004927).length < 2 ^ (prefixWord ++ tailWord_7004927).sum := by decide
  have hdescent : baseEnd_7004927 < baseStart_7004927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004974 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7004974 : Nat := 118140960795 + 7004974 * 2 ^ 59
def prefixEnd_7004974 : Nat := 4983230072969 + 3 ^ 40 * 7004974 * 2
def baseEnd_7004974 : Nat := 3596918634248181240709717

theorem tailTrace_7004974 : CollatzResearch.WordTrace tailWord_7004974 prefixEnd_7004974 3596918634248181240709717 := by
  unfold tailWord_7004974
  simp only [CollatzResearch.WordTrace]
  refine ⟨31936548915522878394709747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170328260882788684771785317 31936548915522878394709747)
  ·
    refine ⟨47904823373284317592064621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31936548915522878394709747 47904823373284317592064621)
    ·
      refine ⟨17964308764981619097024233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47904823373284317592064621 17964308764981619097024233)
      ·
        refine ⟨13473231573736214322768175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17964308764981619097024233 13473231573736214322768175)
        ·
          refine ⟨20209847360604321484152263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13473231573736214322768175 20209847360604321484152263)
          ·
            refine ⟨30314771040906482226228395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20209847360604321484152263 30314771040906482226228395)
            ·
              refine ⟨45472156561359723339342593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30314771040906482226228395 45472156561359723339342593)
              ·
                refine ⟨34104117421019792504506945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45472156561359723339342593 34104117421019792504506945)
                ·
                  refine ⟨25578088065764844378380209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34104117421019792504506945 25578088065764844378380209)
                  ·
                    refine ⟨19183566049323633283785157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25578088065764844378380209 19183566049323633283785157)
                    ·
                      refine ⟨3596918634248181240709717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19183566049323633283785157 3596918634248181240709717)
                      ·
                        rfl

theorem cell23_7004974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7004974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004974 prefixEnd_7004974 := by exact prefixLift 7004974
  have htrace : WordTrace (prefixWord ++ tailWord_7004974) baseStart_7004974 baseEnd_7004974 := by
    simpa [prefixWord, tailWord_7004974, baseEnd_7004974] using wordTrace_append hprefix tailTrace_7004974
  have hstable : (prefixWord ++ tailWord_7004974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004974).length < 2 ^ (prefixWord ++ tailWord_7004974).sum := by decide
  have hdescent : baseEnd_7004974 < baseStart_7004974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7004977 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_7004977 : Nat := 118140960795 + 7004977 * 2 ^ 59
def prefixEnd_7004977 : Nat := 4983230072969 + 3 ^ 40 * 7004977 * 2
def baseEnd_7004977 : Nat := 3596920174690144728972203

theorem tailTrace_7004977 : CollatzResearch.WordTrace tailWord_7004977 prefixEnd_7004977 3596920174690144728972203 := by
  unfold tailWord_7004977
  simp only [CollatzResearch.WordTrace]
  refine ⟨255492500743172158670037185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170328333828781439113358123 255492500743172158670037185)
  ·
    refine ⟨191619375557379119002527889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255492500743172158670037185 191619375557379119002527889)
    ·
      refine ⟨143714531668034339251895917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191619375557379119002527889 143714531668034339251895917)
      ·
        refine ⟨53892949375512877219460969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143714531668034339251895917 53892949375512877219460969)
        ·
          refine ⟨40419712031634657914595727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53892949375512877219460969 40419712031634657914595727)
          ·
            refine ⟨60629568047451986871893591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40419712031634657914595727 60629568047451986871893591)
            ·
              refine ⟨90944352071177980307840387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60629568047451986871893591 90944352071177980307840387)
              ·
                refine ⟨136416528106766970461760581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90944352071177980307840387 136416528106766970461760581)
                ·
                  refine ⟨25578099020018806961580109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136416528106766970461760581 25578099020018806961580109)
                  ·
                    refine ⟨9591787132507052610592541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25578099020018806961580109 9591787132507052610592541)
                    ·
                      refine ⟨3596920174690144728972203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9591787132507052610592541 3596920174690144728972203)
                      ·
                        rfl

theorem cell23_7004977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_7004977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7004977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7004977 prefixEnd_7004977 := by exact prefixLift 7004977
  have htrace : WordTrace (prefixWord ++ tailWord_7004977) baseStart_7004977 baseEnd_7004977 := by
    simpa [prefixWord, tailWord_7004977, baseEnd_7004977] using wordTrace_append hprefix tailTrace_7004977
  have hstable : (prefixWord ++ tailWord_7004977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7004977).length < 2 ^ (prefixWord ++ tailWord_7004977).sum := by decide
  have hdescent : baseEnd_7004977 < baseStart_7004977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7004977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005017 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_7005017 : Nat := 118140960795 + 7005017 * 2 ^ 59
def prefixEnd_7005017 : Nat := 4983230072969 + 3 ^ 40 * 7005017 * 2
def baseEnd_7005017 : Nat := 3596940713916324572472019

theorem tailTrace_7005017 : CollatzResearch.WordTrace tailWord_7005017 prefixEnd_7005017 3596940713916324572472019 := by
  unfold tailWord_7005017
  simp only [CollatzResearch.WordTrace]
  refine ⟨255493959663027245501493305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170329306442018163667662203 255493959663027245501493305)
  ·
    refine ⟨191620469747270434126119979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255493959663027245501493305 191620469747270434126119979)
    ·
      refine ⟨287430704620905651189179969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191620469747270434126119979 287430704620905651189179969)
      ·
        refine ⟨215573028465679238391884977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287430704620905651189179969 215573028465679238391884977)
        ·
          refine ⟨161679771349259428793913733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215573028465679238391884977 161679771349259428793913733)
          ·
            refine ⟨30314957127986142898858825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161679771349259428793913733 30314957127986142898858825)
            ·
              refine ⟨22736217845989607174144119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30314957127986142898858825 22736217845989607174144119)
              ·
                refine ⟨34104326768984410761216179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22736217845989607174144119 34104326768984410761216179)
                ·
                  refine ⟨51156490153476616141824269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34104326768984410761216179 51156490153476616141824269)
                  ·
                    refine ⟨19183683807553731053184101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51156490153476616141824269 19183683807553731053184101)
                    ·
                      refine ⟨3596940713916324572472019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19183683807553731053184101 3596940713916324572472019)
                      ·
                        rfl

theorem cell23_7005017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_7005017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005017 prefixEnd_7005017 := by exact prefixLift 7005017
  have htrace : WordTrace (prefixWord ++ tailWord_7005017) baseStart_7005017 baseEnd_7005017 := by
    simpa [prefixWord, tailWord_7005017, baseEnd_7005017] using wordTrace_append hprefix tailTrace_7005017
  have hstable : (prefixWord ++ tailWord_7005017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005017).length < 2 ^ (prefixWord ++ tailWord_7005017).sum := by decide
  have hdescent : baseEnd_7005017 < baseStart_7005017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005067 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 3]
def baseStart_7005067 : Nat := 118140960795 + 7005067 * 2 ^ 59
def prefixEnd_7005067 : Nat := 4983230072969 + 3 ^ 40 * 7005067 * 2
def baseEnd_7005067 : Nat := 3596966387949049376846789

theorem tailTrace_7005067 : CollatzResearch.WordTrace tailWord_7005067 prefixEnd_7005067 3596966387949049376846789 := by
  unfold tailWord_7005067
  simp only [CollatzResearch.WordTrace]
  refine ⟨255495783312846104040813455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170330522208564069360542303 255495783312846104040813455)
  ·
    refine ⟨383243674969269156061220183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255495783312846104040813455 383243674969269156061220183)
    ·
      refine ⟨574865512453903734091830275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383243674969269156061220183 574865512453903734091830275)
      ·
        refine ⟨862298268680855601137745413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574865512453903734091830275 862298268680855601137745413)
        ·
          refine ⟨161680925377660425213327265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 862298268680855601137745413 161680925377660425213327265)
          ·
            refine ⟨121260694033245318909995449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161680925377660425213327265 121260694033245318909995449)
            ·
              refine ⟨90945520524933989182496587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121260694033245318909995449 90945520524933989182496587)
              ·
                refine ⟨136418280787400983773744881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90945520524933989182496587 136418280787400983773744881)
                ·
                  refine ⟨102313710590550737830308661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136418280787400983773744881 102313710590550737830308661)
                  ·
                    refine ⟨9591910367864131671591437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102313710590550737830308661 9591910367864131671591437)
                    ·
                      refine ⟨3596966387949049376846789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9591910367864131671591437 3596966387949049376846789)
                      ·
                        rfl

theorem cell23_7005067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 3].length) (baseStart_7005067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005067 prefixEnd_7005067 := by exact prefixLift 7005067
  have htrace : WordTrace (prefixWord ++ tailWord_7005067) baseStart_7005067 baseEnd_7005067 := by
    simpa [prefixWord, tailWord_7005067, baseEnd_7005067] using wordTrace_append hprefix tailTrace_7005067
  have hstable : (prefixWord ++ tailWord_7005067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005067).length < 2 ^ (prefixWord ++ tailWord_7005067).sum := by decide
  have hdescent : baseEnd_7005067 < baseStart_7005067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005134 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_7005134 : Nat := 118140960795 + 7005134 * 2 ^ 59
def prefixEnd_7005134 : Nat := 4983230072969 + 3 ^ 40 * 7005134 * 2
def baseEnd_7005134 : Nat := 1199000263717633538236327

theorem tailTrace_7005134 : CollatzResearch.WordTrace tailWord_7005134 prefixEnd_7005134 1199000263717633538236327 := by
  unfold tailWord_7005134
  simp only [CollatzResearch.WordTrace]
  refine ⟨31937278375450421810437807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170332151335735582989001637 31937278375450421810437807)
  ·
    refine ⟨47905917563175632715656711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31937278375450421810437807 47905917563175632715656711)
    ·
      refine ⟨71858876344763449073485067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47905917563175632715656711 71858876344763449073485067)
      ·
        refine ⟨107788314517145173610227601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71858876344763449073485067 107788314517145173610227601)
        ·
          refine ⟨80841235887858880207670701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107788314517145173610227601 80841235887858880207670701)
          ·
            refine ⟨30315463457947080077876513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80841235887858880207670701 30315463457947080077876513)
            ·
              refine ⟨22736597593460310058407385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30315463457947080077876513 22736597593460310058407385)
              ·
                refine ⟨17052448195095232543805539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22736597593460310058407385 17052448195095232543805539)
                ·
                  refine ⟨25578672292642848815708309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17052448195095232543805539 25578672292642848815708309)
                  ·
                    refine ⟨1199000263717633538236327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25578672292642848815708309 1199000263717633538236327)
                    ·
                      rfl

theorem cell23_7005134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_7005134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005134 prefixEnd_7005134 := by exact prefixLift 7005134
  have htrace : WordTrace (prefixWord ++ tailWord_7005134) baseStart_7005134 baseEnd_7005134 := by
    simpa [prefixWord, tailWord_7005134, baseEnd_7005134] using wordTrace_append hprefix tailTrace_7005134
  have hstable : (prefixWord ++ tailWord_7005134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005134).length < 2 ^ (prefixWord ++ tailWord_7005134).sum := by decide
  have hdescent : baseEnd_7005134 < baseStart_7005134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005138 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_7005138 : Nat := 118140960795 + 7005138 * 2 ^ 59
def prefixEnd_7005138 : Nat := 4983230072969 + 3 ^ 40 * 7005138 * 2
def baseEnd_7005138 : Nat := 1199000948358506199686321

theorem tailTrace_7005138 : CollatzResearch.WordTrace tailWord_7005138 prefixEnd_7005138 1199000948358506199686321 := by
  unfold tailWord_7005138
  simp only [CollatzResearch.WordTrace]
  refine ⟨63874593223897220791662017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170332248597059255444432045 63874593223897220791662017)
  ·
    refine ⟨47905944917922915593746513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63874593223897220791662017 47905944917922915593746513)
    ·
      refine ⟨35929458688442186695309885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47905944917922915593746513 35929458688442186695309885)
      ·
        refine ⟨13473547008165820010741207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35929458688442186695309885 13473547008165820010741207)
        ·
          refine ⟨20210320512248730016111811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13473547008165820010741207 20210320512248730016111811)
          ·
            refine ⟨30315480768373095024167717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20210320512248730016111811 30315480768373095024167717)
            ·
              refine ⟨5684152644069955317031447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30315480768373095024167717 5684152644069955317031447)
              ·
                refine ⟨8526228966104932975547171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5684152644069955317031447 8526228966104932975547171)
                ·
                  refine ⟨12789343449157399463320757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8526228966104932975547171 12789343449157399463320757)
                  ·
                    refine ⟨1199000948358506199686321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12789343449157399463320757 1199000948358506199686321)
                    ·
                      rfl

theorem cell23_7005138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_7005138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005138 prefixEnd_7005138 := by exact prefixLift 7005138
  have htrace : WordTrace (prefixWord ++ tailWord_7005138) baseStart_7005138 baseEnd_7005138 := by
    simpa [prefixWord, tailWord_7005138, baseEnd_7005138] using wordTrace_append hprefix tailTrace_7005138
  have hstable : (prefixWord ++ tailWord_7005138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005138).length < 2 ^ (prefixWord ++ tailWord_7005138).sum := by decide
  have hdescent : baseEnd_7005138 < baseStart_7005138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005151 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 4, 4]
def baseStart_7005151 : Nat := 118140960795 + 7005151 * 2 ^ 59
def prefixEnd_7005151 : Nat := 4983230072969 + 3 ^ 40 * 7005151 * 2
def baseEnd_7005151 : Nat := 1199003173441342349398801

theorem tailTrace_7005151 : CollatzResearch.WordTrace tailWord_7005151 prefixEnd_7005151 1199003173441342349398801 := by
  unfold tailWord_7005151
  simp only [CollatzResearch.WordTrace]
  refine ⟨255498847044541786386871307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170332564696361190924580871 255498847044541786386871307)
  ·
    refine ⟨383248270566812679580306961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255498847044541786386871307 383248270566812679580306961)
    ·
      refine ⟨287436202925109509685230221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383248270566812679580306961 287436202925109509685230221)
      ·
        refine ⟨107788576096916066131961333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287436202925109509685230221 107788576096916066131961333)
        ·
          refine ⟨10105179009085881199871375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107788576096916066131961333 10105179009085881199871375)
          ·
            refine ⟨15157768513628821799807063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10105179009085881199871375 15157768513628821799807063)
            ·
              refine ⟨22736652770443232699710595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15157768513628821799807063 22736652770443232699710595)
              ·
                refine ⟨34104979155664849049565893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22736652770443232699710595 34104979155664849049565893)
                ·
                  refine ⟨6394683591687159196793605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34104979155664849049565893 6394683591687159196793605)
                  ·
                    refine ⟨1199003173441342349398801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6394683591687159196793605 1199003173441342349398801)
                    ·
                      rfl

theorem cell23_7005151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 4].length) (baseStart_7005151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005151 prefixEnd_7005151 := by exact prefixLift 7005151
  have htrace : WordTrace (prefixWord ++ tailWord_7005151) baseStart_7005151 baseEnd_7005151 := by
    simpa [prefixWord, tailWord_7005151, baseEnd_7005151] using wordTrace_append hprefix tailTrace_7005151
  have hstable : (prefixWord ++ tailWord_7005151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005151).length < 2 ^ (prefixWord ++ tailWord_7005151).sum := by decide
  have hdescent : baseEnd_7005151 < baseStart_7005151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005186 : List Nat := [3, 4, 1, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7005186 : Nat := 118140960795 + 7005186 * 2 ^ 59
def prefixEnd_7005186 : Nat := 4983230072969 + 3 ^ 40 * 7005186 * 2
def baseEnd_7005186 : Nat := 3597027492146934411258743

theorem tailTrace_7005186 : CollatzResearch.WordTrace tailWord_7005186 prefixEnd_7005186 3597027492146934411258743 := by
  unfold tailWord_7005186
  simp only [CollatzResearch.WordTrace]
  refine ⟨63875030899853746841098853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170333415732943324909596941 63875030899853746841098853)
  ·
    refine ⟨11976568293722577532706035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63875030899853746841098853 11976568293722577532706035)
    ·
      refine ⟨17964852440583866299059053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11976568293722577532706035 17964852440583866299059053)
      ·
        refine ⟨6736819665218949862147145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17964852440583866299059053 6736819665218949862147145)
        ·
          refine ⟨5052614748914212396610359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6736819665218949862147145 5052614748914212396610359)
          ·
            refine ⟨7578922123371318594915539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5052614748914212396610359 7578922123371318594915539)
            ·
              refine ⟨11368383185056977892373309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578922123371318594915539 11368383185056977892373309)
              ·
                refine ⟨4263143694396366709639991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11368383185056977892373309 4263143694396366709639991)
                ·
                  refine ⟨6394715541594550064459987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263143694396366709639991 6394715541594550064459987)
                  ·
                    refine ⟨9592073312391825096689981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6394715541594550064459987 9592073312391825096689981)
                    ·
                      refine ⟨3597027492146934411258743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9592073312391825096689981 3597027492146934411258743)
                      ·
                        rfl

theorem cell23_7005186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7005186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005186 prefixEnd_7005186 := by exact prefixLift 7005186
  have htrace : WordTrace (prefixWord ++ tailWord_7005186) baseStart_7005186 baseEnd_7005186 := by
    simpa [prefixWord, tailWord_7005186, baseEnd_7005186] using wordTrace_append hprefix tailTrace_7005186
  have hstable : (prefixWord ++ tailWord_7005186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005186).length < 2 ^ (prefixWord ++ tailWord_7005186).sum := by decide
  have hdescent : baseEnd_7005186 < baseStart_7005186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005191 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_7005191 : Nat := 118140960795 + 7005191 * 2 ^ 59
def prefixEnd_7005191 : Nat := 4983230072969 + 3 ^ 40 * 7005191 * 2
def baseEnd_7005191 : Nat := 3597030059550206891696219

theorem tailTrace_7005191 : CollatzResearch.WordTrace tailWord_7005191 prefixEnd_7005191 3597030059550206891696219 := by
  unfold tailWord_7005191
  simp only [CollatzResearch.WordTrace]
  refine ⟨255500305964396873218327427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170333537309597915478884951 255500305964396873218327427)
  ·
    refine ⟨383250458946595309827491141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255500305964396873218327427 383250458946595309827491141)
    ·
      refine ⟨71859461052486620592654589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383250458946595309827491141 71859461052486620592654589)
      ·
        refine ⟨26947297894682482722245471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71859461052486620592654589 26947297894682482722245471)
        ·
          refine ⟨40420946842023724083368207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26947297894682482722245471 40420946842023724083368207)
          ·
            refine ⟨60631420263035586125052311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40420946842023724083368207 60631420263035586125052311)
            ·
              refine ⟨90947130394553379187578467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60631420263035586125052311 90947130394553379187578467)
              ·
                refine ⟨136420695591830068781367701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90947130394553379187578467 136420695591830068781367701)
                ·
                  refine ⟨6394720105867034474126611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136420695591830068781367701 6394720105867034474126611)
                  ·
                    refine ⟨9592080158800551711189917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6394720105867034474126611 9592080158800551711189917)
                    ·
                      refine ⟨3597030059550206891696219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9592080158800551711189917 3597030059550206891696219)
                      ·
                        rfl

theorem cell23_7005191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_7005191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005191 prefixEnd_7005191 := by exact prefixLift 7005191
  have htrace : WordTrace (prefixWord ++ tailWord_7005191) baseStart_7005191 baseEnd_7005191 := by
    simpa [prefixWord, tailWord_7005191, baseEnd_7005191] using wordTrace_append hprefix tailTrace_7005191
  have hstable : (prefixWord ++ tailWord_7005191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005191).length < 2 ^ (prefixWord ++ tailWord_7005191).sum := by decide
  have hdescent : baseEnd_7005191 < baseStart_7005191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005192 : List Nat := [2, 1, 3, 2, 1, 5, 1, 3, 1, 2, 2]
def baseStart_7005192 : Nat := 118140960795 + 7005192 * 2 ^ 59
def prefixEnd_7005192 : Nat := 4983230072969 + 3 ^ 40 * 7005192 * 2
def baseEnd_7005192 : Nat := 3597030573030861387783715

theorem tailTrace_7005192 : CollatzResearch.WordTrace tailWord_7005192 prefixEnd_7005192 3597030573030861387783715 := by
  unfold tailWord_7005192
  simp only [CollatzResearch.WordTrace]
  refine ⟨127750171218696625194556915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170333561624928833592742553 127750171218696625194556915)
  ·
    refine ⟨191625256828044937791835373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127750171218696625194556915 191625256828044937791835373)
    ·
      refine ⟨71859471310516851671938265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191625256828044937791835373 71859471310516851671938265)
      ·
        refine ⟨53894603482887638753953699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71859471310516851671938265 53894603482887638753953699)
        ·
          refine ⟨80841905224331458130930549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53894603482887638753953699 80841905224331458130930549)
          ·
            refine ⟨7578928614781074199774739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80841905224331458130930549 7578928614781074199774739)
            ·
              refine ⟨11368392922171611299662109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578928614781074199774739 11368392922171611299662109)
              ·
                refine ⟨4263147345814354237373291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11368392922171611299662109 4263147345814354237373291)
                ·
                  refine ⟨6394721018721531356059937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263147345814354237373291 6394721018721531356059937)
                  ·
                    refine ⟨4796040764041148517044953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6394721018721531356059937 4796040764041148517044953)
                    ·
                      refine ⟨3597030573030861387783715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796040764041148517044953 3597030573030861387783715)
                      ·
                        rfl

theorem cell23_7005192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_7005192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005192 prefixEnd_7005192 := by exact prefixLift 7005192
  have htrace : WordTrace (prefixWord ++ tailWord_7005192) baseStart_7005192 baseEnd_7005192 := by
    simpa [prefixWord, tailWord_7005192, baseEnd_7005192] using wordTrace_append hprefix tailTrace_7005192
  have hstable : (prefixWord ++ tailWord_7005192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005192).length < 2 ^ (prefixWord ++ tailWord_7005192).sum := by decide
  have hdescent : baseEnd_7005192 < baseStart_7005192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005234 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_7005234 : Nat := 118140960795 + 7005234 * 2 ^ 59
def prefixEnd_7005234 : Nat := 4983230072969 + 3 ^ 40 * 7005234 * 2
def baseEnd_7005234 : Nat := 3597052139218350223458521

theorem tailTrace_7005234 : CollatzResearch.WordTrace tailWord_7005234 prefixEnd_7005234 3597052139218350223458521 := by
  unfold tailWord_7005234
  simp only [CollatzResearch.WordTrace]
  refine ⟨63875468575810272890535689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170334582868827394374761837 63875468575810272890535689)
  ·
    refine ⟨47906601431857704667901767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63875468575810272890535689 47906601431857704667901767)
    ·
      refine ⟨71859902147786557001852651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47906601431857704667901767 71859902147786557001852651)
      ·
        refine ⟨107789853221679835502778977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71859902147786557001852651 107789853221679835502778977)
        ·
          refine ⟨80842389916259876627084233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107789853221679835502778977 80842389916259876627084233)
          ·
            refine ⟨60631792437194907470313175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80842389916259876627084233 60631792437194907470313175)
            ·
              refine ⟨90947688655792361205469763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60631792437194907470313175 90947688655792361205469763)
              ·
                refine ⟨136421532983688541808204645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90947688655792361205469763 136421532983688541808204645)
                ·
                  refine ⟨25579037434441601589038371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136421532983688541808204645 25579037434441601589038371)
                  ·
                    refine ⟨38368556151662402383557557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25579037434441601589038371 38368556151662402383557557)
                    ·
                      refine ⟨3597052139218350223458521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38368556151662402383557557 3597052139218350223458521)
                      ·
                        rfl

theorem cell23_7005234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_7005234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005234 prefixEnd_7005234 := by exact prefixLift 7005234
  have htrace : WordTrace (prefixWord ++ tailWord_7005234) baseStart_7005234 baseEnd_7005234 := by
    simpa [prefixWord, tailWord_7005234, baseEnd_7005234] using wordTrace_append hprefix tailTrace_7005234
  have hstable : (prefixWord ++ tailWord_7005234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005234).length < 2 ^ (prefixWord ++ tailWord_7005234).sum := by decide
  have hdescent : baseEnd_7005234 < baseStart_7005234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005264 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 3]
def baseStart_7005264 : Nat := 118140960795 + 7005264 * 2 ^ 59
def prefixEnd_7005264 : Nat := 4983230072969 + 3 ^ 40 * 7005264 * 2
def baseEnd_7005264 : Nat := 3597067543637985106083383

theorem tailTrace_7005264 : CollatzResearch.WordTrace tailWord_7005264 prefixEnd_7005264 3597067543637985106083383 := by
  unfold tailWord_7005264
  simp only [CollatzResearch.WordTrace]
  refine ⟨127751484246566203342867423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170335312328754937790489897 127751484246566203342867423)
  ·
    refine ⟨191627226369849305014301135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127751484246566203342867423 191627226369849305014301135)
    ·
      refine ⟨287440839554773957521451703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191627226369849305014301135 287440839554773957521451703)
      ·
        refine ⟨431161259332160936282177555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287440839554773957521451703 431161259332160936282177555)
        ·
          refine ⟨646741888998241404423266333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431161259332160936282177555 646741888998241404423266333)
          ·
            refine ⟨242528208374340526658724875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 646741888998241404423266333 242528208374340526658724875)
            ·
              refine ⟨363792312561510789988087313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242528208374340526658724875 363792312561510789988087313)
              ·
                refine ⟨272844234421133092491065485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363792312561510789988087313 272844234421133092491065485)
                ·
                  refine ⟨102316587907924909684149557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272844234421133092491065485 102316587907924909684149557)
                  ·
                    refine ⟨9592180116367960282889021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102316587907924909684149557 9592180116367960282889021)
                    ·
                      refine ⟨3597067543637985106083383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9592180116367960282889021 3597067543637985106083383)
                      ·
                        rfl

theorem cell23_7005264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_7005264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005264 prefixEnd_7005264 := by exact prefixLift 7005264
  have htrace : WordTrace (prefixWord ++ tailWord_7005264) baseStart_7005264 baseEnd_7005264 := by
    simpa [prefixWord, tailWord_7005264, baseEnd_7005264] using wordTrace_append hprefix tailTrace_7005264
  have hstable : (prefixWord ++ tailWord_7005264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005264).length < 2 ^ (prefixWord ++ tailWord_7005264).sum := by decide
  have hdescent : baseEnd_7005264 < baseStart_7005264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005282 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7005282 : Nat := 118140960795 + 7005282 * 2 ^ 59
def prefixEnd_7005282 : Nat := 4983230072969 + 3 ^ 40 * 7005282 * 2
def baseEnd_7005282 : Nat := 3597076786289766035658301

theorem tailTrace_7005282 : CollatzResearch.WordTrace tailWord_7005282 prefixEnd_7005282 3597076786289766035658301 := by
  unfold tailWord_7005282
  simp only [CollatzResearch.WordTrace]
  refine ⟨63875906251766798939972525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170335750004711463839926733 63875906251766798939972525)
  ·
    refine ⟨23953464844412549602489697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63875906251766798939972525 23953464844412549602489697)
    ·
      refine ⟨17965098633309412201867273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23953464844412549602489697 17965098633309412201867273)
      ·
        refine ⟨13473823974982059151400455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17965098633309412201867273 13473823974982059151400455)
        ·
          refine ⟨20210735962473088727100683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13473823974982059151400455 20210735962473088727100683)
          ·
            refine ⟨30316103943709633090651025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20210735962473088727100683 30316103943709633090651025)
            ·
              refine ⟨22737077957782224817988269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30316103943709633090651025 22737077957782224817988269)
              ·
                refine ⟨8526404234168334306745601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22737077957782224817988269 8526404234168334306745601)
                ·
                  refine ⟨6394803175626250730059201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8526404234168334306745601 6394803175626250730059201)
                  ·
                    refine ⟨4796102381719688047544401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6394803175626250730059201 4796102381719688047544401)
                    ·
                      refine ⟨3597076786289766035658301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796102381719688047544401 3597076786289766035658301)
                      ·
                        rfl

theorem cell23_7005282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7005282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005282 prefixEnd_7005282 := by exact prefixLift 7005282
  have htrace : WordTrace (prefixWord ++ tailWord_7005282) baseStart_7005282 baseEnd_7005282 := by
    simpa [prefixWord, tailWord_7005282, baseEnd_7005282] using wordTrace_append hprefix tailTrace_7005282
  have hstable : (prefixWord ++ tailWord_7005282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005282).length < 2 ^ (prefixWord ++ tailWord_7005282).sum := by decide
  have hdescent : baseEnd_7005282 < baseStart_7005282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005284 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_7005284 : Nat := 118140960795 + 7005284 * 2 ^ 59
def prefixEnd_7005284 : Nat := 4983230072969 + 3 ^ 40 * 7005284 * 2
def baseEnd_7005284 : Nat := 1199025937750358342611097

theorem tailTrace_7005284 : CollatzResearch.WordTrace tailWord_7005284 prefixEnd_7005284 1199025937750358342611097 := by
  unfold tailWord_7005284
  simp only [CollatzResearch.WordTrace]
  refine ⟨127751848976529975050731453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170335798635373300067641937 127751848976529975050731453)
  ·
    refine ⟨47906943366198740644024295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127751848976529975050731453 47906943366198740644024295)
    ·
      refine ⟨71860415049298110966036443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47906943366198740644024295 71860415049298110966036443)
      ·
        refine ⟨107790622573947166449054665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71860415049298110966036443 107790622573947166449054665)
        ·
          refine ⟨80842966930460374836790999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107790622573947166449054665 80842966930460374836790999)
          ·
            refine ⟨121264450395690562255186499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80842966930460374836790999 121264450395690562255186499)
            ·
              refine ⟨181896675593535843382779749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121264450395690562255186499 181896675593535843382779749)
              ·
                refine ⟨34105626673787970634271203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181896675593535843382779749 34105626673787970634271203)
                ·
                  refine ⟨51158440010681955951406805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34105626673787970634271203 51158440010681955951406805)
                  ·
                    refine ⟨1199025937750358342611097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51158440010681955951406805 1199025937750358342611097)
                    ·
                      rfl

theorem cell23_7005284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_7005284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005284 prefixEnd_7005284 := by exact prefixLift 7005284
  have htrace : WordTrace (prefixWord ++ tailWord_7005284) baseStart_7005284 baseEnd_7005284 := by
    simpa [prefixWord, tailWord_7005284, baseEnd_7005284] using wordTrace_append hprefix tailTrace_7005284
  have hstable : (prefixWord ++ tailWord_7005284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005284).length < 2 ^ (prefixWord ++ tailWord_7005284).sum := by decide
  have hdescent : baseEnd_7005284 < baseStart_7005284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005288 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 7]
def baseStart_7005288 : Nat := 118140960795 + 7005288 * 2 ^ 59
def prefixEnd_7005288 : Nat := 4983230072969 + 3 ^ 40 * 7005288 * 2
def baseEnd_7005288 : Nat := 399675540797077001353697

theorem tailTrace_7005288 : CollatzResearch.WordTrace tailWord_7005288 prefixEnd_7005288 399675540797077001353697 := by
  unfold tailWord_7005288
  simp only [CollatzResearch.WordTrace]
  refine ⟨127751921922522729392304259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170335895896696972523072345 127751921922522729392304259)
  ·
    refine ⟨191627882883784094088456389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127751921922522729392304259 191627882883784094088456389)
    ·
      refine ⟨35930228040709517641585573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191627882883784094088456389 35930228040709517641585573)
      ·
        refine ⟨6736917757633034557797295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35930228040709517641585573 6736917757633034557797295)
        ·
          refine ⟨10105376636449551836695943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736917757633034557797295 10105376636449551836695943)
          ·
            refine ⟨15158064954674327755043915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10105376636449551836695943 15158064954674327755043915)
            ·
              refine ⟨22737097432011491632565873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15158064954674327755043915 22737097432011491632565873)
              ·
                refine ⟨17052823074008618724424405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22737097432011491632565873 17052823074008618724424405)
                ·
                  refine ⟨399675540797077001353697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17052823074008618724424405 399675540797077001353697)
                  ·
                    rfl

theorem cell23_7005288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 7].length) (baseStart_7005288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005288 prefixEnd_7005288 := by exact prefixLift 7005288
  have htrace : WordTrace (prefixWord ++ tailWord_7005288) baseStart_7005288 baseEnd_7005288 := by
    simpa [prefixWord, tailWord_7005288, baseEnd_7005288] using wordTrace_append hprefix tailTrace_7005288
  have hstable : (prefixWord ++ tailWord_7005288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005288).length < 2 ^ (prefixWord ++ tailWord_7005288).sum := by decide
  have hdescent : baseEnd_7005288 < baseStart_7005288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005324 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7005324 : Nat := 118140960795 + 7005324 * 2 ^ 59
def prefixEnd_7005324 : Nat := 4983230072969 + 3 ^ 40 * 7005324 * 2
def baseEnd_7005324 : Nat := 3597098352477254871333107

theorem tailTrace_7005324 : CollatzResearch.WordTrace tailWord_7005324 prefixEnd_7005324 3597098352477254871333107 := by
  unfold tailWord_7005324
  simp only [CollatzResearch.WordTrace]
  refine ⟨127752578436457518466459513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170336771248610024621946017 127752578436457518466459513)
  ·
    refine ⟨95814433827343138849844635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127752578436457518466459513 95814433827343138849844635)
    ·
      refine ⟨143721650741014708274766953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95814433827343138849844635 143721650741014708274766953)
      ·
        refine ⟨107791238055761031206075215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143721650741014708274766953 107791238055761031206075215)
        ·
          refine ⟨161686857083641546809112823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107791238055761031206075215 161686857083641546809112823)
          ·
            refine ⟨242530285625462320213669235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161686857083641546809112823 242530285625462320213669235)
            ·
              refine ⟨363795428438193480320503853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242530285625462320213669235 363795428438193480320503853)
              ·
                refine ⟨136423285664322555120188945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363795428438193480320503853 136423285664322555120188945)
                ·
                  refine ⟨102317464248241916340141709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136423285664322555120188945 102317464248241916340141709)
                  ·
                    refine ⟨38369049093090718627553141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102317464248241916340141709 38369049093090718627553141)
                    ·
                      refine ⟨3597098352477254871333107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38369049093090718627553141 3597098352477254871333107)
                      ·
                        rfl

theorem cell23_7005324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7005324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005324 prefixEnd_7005324 := by exact prefixLift 7005324
  have htrace : WordTrace (prefixWord ++ tailWord_7005324) baseStart_7005324 baseEnd_7005324 := by
    simpa [prefixWord, tailWord_7005324, baseEnd_7005324] using wordTrace_append hprefix tailTrace_7005324
  have hstable : (prefixWord ++ tailWord_7005324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005324).length < 2 ^ (prefixWord ++ tailWord_7005324).sum := by decide
  have hdescent : baseEnd_7005324 < baseStart_7005324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005331 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 3, 4]
def baseStart_7005331 : Nat := 118140960795 + 7005331 * 2 ^ 59
def prefixEnd_7005331 : Nat := 4983230072969 + 3 ^ 40 * 7005331 * 2
def baseEnd_7005331 : Nat := 1199033982280612114648525

theorem tailTrace_7005331 : CollatzResearch.WordTrace tailWord_7005331 prefixEnd_7005331 1199033982280612114648525 := by
  unfold tailWord_7005331
  simp only [CollatzResearch.WordTrace]
  refine ⟨255505412183889677128423847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170336941455926451418949231 255505412183889677128423847)
  ·
    refine ⟨383258118275834515692635771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255505412183889677128423847 383258118275834515692635771)
    ·
      refine ⟨574887177413751773538953657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383258118275834515692635771 574887177413751773538953657)
      ·
        refine ⟨431165383060313830154215243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574887177413751773538953657 431165383060313830154215243)
        ·
          refine ⟨646748074590470745231322865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431165383060313830154215243 646748074590470745231322865)
          ·
            refine ⟨485061055942853058923492149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646748074590470745231322865 485061055942853058923492149)
            ·
              refine ⟨45474473994642474274077389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 485061055942853058923492149 45474473994642474274077389)
              ·
                refine ⟨17052927747990927852779021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45474473994642474274077389 17052927747990927852779021)
                ·
                  refine ⟨6394847905496597944792133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17052927747990927852779021 6394847905496597944792133)
                  ·
                    refine ⟨1199033982280612114648525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6394847905496597944792133 1199033982280612114648525)
                    ·
                      rfl

theorem cell23_7005331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 4].length) (baseStart_7005331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005331 prefixEnd_7005331 := by exact prefixLift 7005331
  have htrace : WordTrace (prefixWord ++ tailWord_7005331) baseStart_7005331 baseEnd_7005331 := by
    simpa [prefixWord, tailWord_7005331, baseEnd_7005331] using wordTrace_append hprefix tailTrace_7005331
  have hstable : (prefixWord ++ tailWord_7005331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005331).length < 2 ^ (prefixWord ++ tailWord_7005331).sum := by decide
  have hdescent : baseEnd_7005331 < baseStart_7005331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005341 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_7005341 : Nat := 118140960795 + 7005341 * 2 ^ 59
def prefixEnd_7005341 : Nat := 4983230072969 + 3 ^ 40 * 7005341 * 2
def baseEnd_7005341 : Nat := 3597107081648381304820529

theorem tailTrace_7005341 : CollatzResearch.WordTrace tailWord_7005341 prefixEnd_7005341 3597107081648381304820529 := by
  unfold tailWord_7005341
  simp only [CollatzResearch.WordTrace]
  refine ⟨255505776913853448836287877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170337184609235632557525251 255505776913853448836287877)
  ·
    refine ⟨47907333171347521656803977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255505776913853448836287877 47907333171347521656803977)
    ·
      refine ⟨35930499878510641242602983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47907333171347521656803977 35930499878510641242602983)
      ·
        refine ⟨53895749817765961863904475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35930499878510641242602983 53895749817765961863904475)
        ·
          refine ⟨80843624726648942795856713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53895749817765961863904475 80843624726648942795856713)
          ·
            refine ⟨60632718544986707096892535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80843624726648942795856713 60632718544986707096892535)
            ·
              refine ⟨90949077817480060645338803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60632718544986707096892535 90949077817480060645338803)
              ·
                refine ⟨136423616726220090968008205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90949077817480060645338803 136423616726220090968008205)
                ·
                  refine ⟨51158856272332534113003077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136423616726220090968008205 51158856272332534113003077)
                  ·
                    refine ⟨9592285551062350146188077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51158856272332534113003077 9592285551062350146188077)
                    ·
                      refine ⟨3597107081648381304820529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9592285551062350146188077 3597107081648381304820529)
                      ·
                        rfl

theorem cell23_7005341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_7005341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005341 prefixEnd_7005341 := by exact prefixLift 7005341
  have htrace : WordTrace (prefixWord ++ tailWord_7005341) baseStart_7005341 baseEnd_7005341 := by
    simpa [prefixWord, tailWord_7005341, baseEnd_7005341] using wordTrace_append hprefix tailTrace_7005341
  have hstable : (prefixWord ++ tailWord_7005341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005341).length < 2 ^ (prefixWord ++ tailWord_7005341).sum := by decide
  have hdescent : baseEnd_7005341 < baseStart_7005341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005348 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_7005348 : Nat := 118140960795 + 7005348 * 2 ^ 59
def prefixEnd_7005348 : Nat := 4983230072969 + 3 ^ 40 * 7005348 * 2
def baseEnd_7005348 : Nat := 1199036892004320925810999

theorem tailTrace_7005348 : CollatzResearch.WordTrace tailWord_7005348 prefixEnd_7005348 1199036892004320925810999 := by
  unfold tailWord_7005348
  simp only [CollatzResearch.WordTrace]
  refine ⟨127753016112414044515896349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170337354816552059354528465 127753016112414044515896349)
  ·
    refine ⟨47907381042155266693461131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127753016112414044515896349 47907381042155266693461131)
    ·
      refine ⟨71861071563232900040191697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47907381042155266693461131 71861071563232900040191697)
      ·
        refine ⟨53895803672424675030143773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71861071563232900040191697 53895803672424675030143773)
        ·
          refine ⟨20210926377159253136303915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53895803672424675030143773 20210926377159253136303915)
          ·
            refine ⟨30316389565738879704455873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20210926377159253136303915 30316389565738879704455873)
            ·
              refine ⟨22737292174304159778341905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30316389565738879704455873 22737292174304159778341905)
              ·
                refine ⟨17052969130728119833756429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22737292174304159778341905 17052969130728119833756429)
                ·
                  refine ⟨6394863424023044937658661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17052969130728119833756429 6394863424023044937658661)
                  ·
                    refine ⟨1199036892004320925810999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6394863424023044937658661 1199036892004320925810999)
                    ·
                      rfl

theorem cell23_7005348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_7005348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005348 prefixEnd_7005348 := by exact prefixLift 7005348
  have htrace : WordTrace (prefixWord ++ tailWord_7005348) baseStart_7005348 baseEnd_7005348 := by
    simpa [prefixWord, tailWord_7005348, baseEnd_7005348] using wordTrace_append hprefix tailTrace_7005348
  have hstable : (prefixWord ++ tailWord_7005348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005348).length < 2 ^ (prefixWord ++ tailWord_7005348).sum := by decide
  have hdescent : baseEnd_7005348 < baseStart_7005348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005361 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 8]
def baseStart_7005361 : Nat := 118140960795 + 7005361 * 2 ^ 59
def prefixEnd_7005361 : Nat := 4983230072969 + 3 ^ 40 * 7005361 * 2
def baseEnd_7005361 : Nat := 399679705695719025174493

theorem tailTrace_7005361 : CollatzResearch.WordTrace tailWord_7005361 prefixEnd_7005361 399679705695719025174493 := by
  unfold tailWord_7005361
  simp only [CollatzResearch.WordTrace]
  refine ⟨255506506373780992252015937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170337670915853994834677291 255506506373780992252015937)
  ·
    refine ⟨191629879780335744189011953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255506506373780992252015937 191629879780335744189011953)
    ·
      refine ⟨143722409835251808141758965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191629879780335744189011953 143722409835251808141758965)
      ·
        refine ⟨13473975922054857013289903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143722409835251808141758965 13473975922054857013289903)
        ·
          refine ⟨20210963883082285519934855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13473975922054857013289903 20210963883082285519934855)
          ·
            refine ⟨30316445824623428279902283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20210963883082285519934855 30316445824623428279902283)
            ·
              refine ⟨45474668736935142419853425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30316445824623428279902283 45474668736935142419853425)
              ·
                refine ⟨34106001552701356814890069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45474668736935142419853425 34106001552701356814890069)
                ·
                  refine ⟨399679705695719025174493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34106001552701356814890069 399679705695719025174493)
                  ·
                    rfl

theorem cell23_7005361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 8].length) (baseStart_7005361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005361 prefixEnd_7005361 := by exact prefixLift 7005361
  have htrace : WordTrace (prefixWord ++ tailWord_7005361) baseStart_7005361 baseEnd_7005361 := by
    simpa [prefixWord, tailWord_7005361, baseEnd_7005361] using wordTrace_append hprefix tailTrace_7005361
  have hstable : (prefixWord ++ tailWord_7005361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005361).length < 2 ^ (prefixWord ++ tailWord_7005361).sum := by decide
  have hdescent : baseEnd_7005361 < baseStart_7005361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005408 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 1, 5]
def baseStart_7005408 : Nat := 118140960795 + 7005408 * 2 ^ 59
def prefixEnd_7005408 : Nat := 4983230072969 + 3 ^ 40 * 7005408 * 2
def baseEnd_7005408 : Nat := 1199047161617410847560907

theorem tailTrace_7005408 : CollatzResearch.WordTrace tailWord_7005408 prefixEnd_7005408 1199047161617410847560907 := by
  unfold tailWord_7005408
  simp only [CollatzResearch.WordTrace]
  refine ⟨127754110302305359639488439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170338813736407146185984585 127754110302305359639488439)
  ·
    refine ⟨191631165453458039459232659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127754110302305359639488439 191631165453458039459232659)
    ·
      refine ⟨287446748180187059188848989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191631165453458039459232659 287446748180187059188848989)
      ·
        refine ⟨107792530567570147195818371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287446748180187059188848989 107792530567570147195818371)
        ·
          refine ⟨161688795851355220793727557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107792530567570147195818371 161688795851355220793727557)
          ·
            refine ⟨30316649222129103898823917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161688795851355220793727557 30316649222129103898823917)
            ·
              refine ⟨11368743458298413962058969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30316649222129103898823917 11368743458298413962058969)
              ·
                refine ⟨8526557593723810471544227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11368743458298413962058969 8526557593723810471544227)
                ·
                  refine ⟨12789836390585715707316341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8526557593723810471544227 12789836390585715707316341)
                  ·
                    refine ⟨1199047161617410847560907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12789836390585715707316341 1199047161617410847560907)
                    ·
                      rfl

theorem cell23_7005408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 5].length) (baseStart_7005408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005408 prefixEnd_7005408 := by exact prefixLift 7005408
  have htrace : WordTrace (prefixWord ++ tailWord_7005408) baseStart_7005408 baseEnd_7005408 := by
    simpa [prefixWord, tailWord_7005408, baseEnd_7005408] using wordTrace_append hprefix tailTrace_7005408
  have hstable : (prefixWord ++ tailWord_7005408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005408).length < 2 ^ (prefixWord ++ tailWord_7005408).sum := by decide
  have hdescent : baseEnd_7005408 < baseStart_7005408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005439 : List Nat := [1, 1, 2, 2, 1, 7, 2, 2, 1, 1, 3]
def baseStart_7005439 : Nat := 118140960795 + 7005439 * 2 ^ 59
def prefixEnd_7005439 : Nat := 4983230072969 + 3 ^ 40 * 7005439 * 2
def baseEnd_7005439 : Nat := 3597157402752521921395079

theorem tailTrace_7005439 : CollatzResearch.WordTrace tailWord_7005439 prefixEnd_7005439 3597157402752521921395079 := by
  unfold tailWord_7005439
  simp only [CollatzResearch.WordTrace]
  refine ⟨255509351267498411573355371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170339567511665607715570247 255509351267498411573355371)
  ·
    refine ⟨383264026901247617360033057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255509351267498411573355371 383264026901247617360033057)
    ·
      refine ⟨287448020175935713020024793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383264026901247617360033057 287448020175935713020024793)
      ·
        refine ⟨215586015131951784765018595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287448020175935713020024793 215586015131951784765018595)
        ·
          refine ⟨323379022697927677147527893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215586015131951784765018595 323379022697927677147527893)
          ·
            refine ⟨7579195844482679933145185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 323379022697927677147527893 7579195844482679933145185)
            ·
              refine ⟨5684396883362009949858889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7579195844482679933145185 5684396883362009949858889)
              ·
                refine ⟨4263297662521507462394167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5684396883362009949858889 4263297662521507462394167)
                ·
                  refine ⟨6394946493782261193591251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263297662521507462394167 6394946493782261193591251)
                  ·
                    refine ⟨9592419740673391790386877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6394946493782261193591251 9592419740673391790386877)
                    ·
                      refine ⟨3597157402752521921395079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9592419740673391790386877 3597157402752521921395079)
                      ·
                        rfl

theorem cell23_7005439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 1, 3].length) (baseStart_7005439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005439 prefixEnd_7005439 := by exact prefixLift 7005439
  have htrace : WordTrace (prefixWord ++ tailWord_7005439) baseStart_7005439 baseEnd_7005439 := by
    simpa [prefixWord, tailWord_7005439, baseEnd_7005439] using wordTrace_append hprefix tailTrace_7005439
  have hstable : (prefixWord ++ tailWord_7005439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005439).length < 2 ^ (prefixWord ++ tailWord_7005439).sum := by decide
  have hdescent : baseEnd_7005439 < baseStart_7005439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005445 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 3, 2, 2]
def baseStart_7005445 : Nat := 118140960795 + 7005445 * 2 ^ 59
def prefixEnd_7005445 : Nat := 4983230072969 + 3 ^ 40 * 7005445 * 2
def baseEnd_7005445 : Nat := 3597160483636448897920051

theorem tailTrace_7005445 : CollatzResearch.WordTrace tailWord_7005445 prefixEnd_7005445 3597160483636448897920051 := by
  unfold tailWord_7005445
  simp only [CollatzResearch.WordTrace]
  refine ⟨255509570105476674598073789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170339713403651116398715859 255509570105476674598073789)
  ·
    refine ⟨95816088789553752974277671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255509570105476674598073789 95816088789553752974277671)
    ·
      refine ⟨143724133184330629461416507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95816088789553752974277671 143724133184330629461416507)
      ·
        refine ⟨215586199776495944192124761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143724133184330629461416507 215586199776495944192124761)
        ·
          refine ⟨161689649832371958144093571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215586199776495944192124761 161689649832371958144093571)
          ·
            refine ⟨242534474748557937216140357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161689649832371958144093571 242534474748557937216140357)
            ·
              refine ⟨45475214015354613228026317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242534474748557937216140357 45475214015354613228026317)
              ·
                refine ⟨17053205255757979960509869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45475214015354613228026317 17053205255757979960509869)
                ·
                  refine ⟨6394951970909242485191201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17053205255757979960509869 6394951970909242485191201)
                  ·
                    refine ⟨4796213978181931863893401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6394951970909242485191201 4796213978181931863893401)
                    ·
                      refine ⟨3597160483636448897920051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796213978181931863893401 3597160483636448897920051)
                      ·
                        rfl

theorem cell23_7005445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_7005445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005445 prefixEnd_7005445 := by exact prefixLift 7005445
  have htrace : WordTrace (prefixWord ++ tailWord_7005445) baseStart_7005445 baseEnd_7005445 := by
    simpa [prefixWord, tailWord_7005445, baseEnd_7005445] using wordTrace_append hprefix tailTrace_7005445
  have hstable : (prefixWord ++ tailWord_7005445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005445).length < 2 ^ (prefixWord ++ tailWord_7005445).sum := by decide
  have hdescent : baseEnd_7005445 < baseStart_7005445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005451 : List Nat := [1, 1, 1, 1, 5, 3, 3, 8]
def baseStart_7005451 : Nat := 118140960795 + 7005451 * 2 ^ 59
def prefixEnd_7005451 : Nat := 4983230072969 + 3 ^ 40 * 7005451 * 2
def baseEnd_7005451 : Nat := 133228280167421328683149

theorem tailTrace_7005451 : CollatzResearch.WordTrace tailWord_7005451 prefixEnd_7005451 133228280167421328683149 := by
  unfold tailWord_7005451
  simp only [CollatzResearch.WordTrace]
  refine ⟨255509788943454937622792207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170339859295636625081861471 255509788943454937622792207)
  ·
    refine ⟨383264683415182406434188311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255509788943454937622792207 383264683415182406434188311)
    ·
      refine ⟨574897025122773609651282467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383264683415182406434188311 574897025122773609651282467)
      ·
        refine ⟨862345537684160414476923701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574897025122773609651282467 862345537684160414476923701)
        ·
          refine ⟨80844894157890038857211597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 862345537684160414476923701 80844894157890038857211597)
          ·
            refine ⟨30316835309208764571454349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80844894157890038857211597 30316835309208764571454349)
            ·
              refine ⟨11368813240953286714295381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30316835309208764571454349 11368813240953286714295381)
              ·
                refine ⟨133228280167421328683149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11368813240953286714295381 133228280167421328683149)
                ·
                  rfl

theorem cell23_7005451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 8].length) (baseStart_7005451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005451 prefixEnd_7005451 := by exact prefixLift 7005451
  have htrace : WordTrace (prefixWord ++ tailWord_7005451) baseStart_7005451 baseEnd_7005451 := by
    simpa [prefixWord, tailWord_7005451, baseEnd_7005451] using wordTrace_append hprefix tailTrace_7005451
  have hstable : (prefixWord ++ tailWord_7005451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005451).length < 2 ^ (prefixWord ++ tailWord_7005451).sum := by decide
  have hdescent : baseEnd_7005451 < baseStart_7005451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005482 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_7005482 : Nat := 118140960795 + 7005482 * 2 ^ 59
def prefixEnd_7005482 : Nat := 4983230072969 + 3 ^ 40 * 7005482 * 2
def baseEnd_7005482 : Nat := 3597179482420665253157381

theorem tailTrace_7005482 : CollatzResearch.WordTrace tailWord_7005482 prefixEnd_7005482 3597179482420665253157381 := by
  unfold tailWord_7005482
  simp only [CollatzResearch.WordTrace]
  refine ⟨63877729901585657479292675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170340613070895086611447133 63877729901585657479292675)
  ·
    refine ⟨95816594852378486218939013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63877729901585657479292675 95816594852378486218939013)
    ·
      refine ⟨17965611534820966166051065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95816594852378486218939013 17965611534820966166051065)
      ·
        refine ⟨13474208651115724624538299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17965611534820966166051065 13474208651115724624538299)
        ·
          refine ⟨20211312976673586936807449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13474208651115724624538299 20211312976673586936807449)
          ·
            refine ⟨15158484732505190202605587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20211312976673586936807449 15158484732505190202605587)
            ·
              refine ⟨22737727098757785303908381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15158484732505190202605587 22737727098757785303908381)
              ·
                refine ⟨8526647662034169488965643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22737727098757785303908381 8526647662034169488965643)
                ·
                  refine ⟨12789971493051254233448465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8526647662034169488965643 12789971493051254233448465)
                  ·
                    refine ⟨9592478619788440675086349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12789971493051254233448465 9592478619788440675086349)
                    ·
                      refine ⟨3597179482420665253157381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9592478619788440675086349 3597179482420665253157381)
                      ·
                        rfl

theorem cell23_7005482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_7005482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005482 prefixEnd_7005482 := by exact prefixLift 7005482
  have htrace : WordTrace (prefixWord ++ tailWord_7005482) baseStart_7005482 baseEnd_7005482 := by
    simpa [prefixWord, tailWord_7005482, baseEnd_7005482] using wordTrace_append hprefix tailTrace_7005482
  have hstable : (prefixWord ++ tailWord_7005482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005482).length < 2 ^ (prefixWord ++ tailWord_7005482).sum := by decide
  have hdescent : baseEnd_7005482 < baseStart_7005482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005551 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_7005551 : Nat := 118140960795 + 7005551 * 2 ^ 59
def prefixEnd_7005551 : Nat := 4983230072969 + 3 ^ 40 * 7005551 * 2
def baseEnd_7005551 : Nat := 3597214912585825483194563

theorem tailTrace_7005551 : CollatzResearch.WordTrace tailWord_7005551 prefixEnd_7005551 3597214912585825483194563 := by
  unfold tailWord_7005551
  simp only [CollatzResearch.WordTrace]
  refine ⟨255513436243092654701432507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170342290828728436467621671 255513436243092654701432507)
  ·
    refine ⟨383270154364638982052148761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255513436243092654701432507 383270154364638982052148761)
    ·
      refine ⟨287452615773479236539111571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383270154364638982052148761 287452615773479236539111571)
      ·
        refine ⟨431178923660218854808667357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287452615773479236539111571 431178923660218854808667357)
        ·
          refine ⟨161692096372582070553250259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431178923660218854808667357 161692096372582070553250259)
          ·
            refine ⟨242538144558873105829875389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161692096372582070553250259 242538144558873105829875389)
            ·
              refine ⟨90951804209577414686203271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242538144558873105829875389 90951804209577414686203271)
              ·
                refine ⟨136427706314366122029304907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90951804209577414686203271 136427706314366122029304907)
                ·
                  refine ⟨204641559471549183043957361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136427706314366122029304907 204641559471549183043957361)
                  ·
                    refine ⟨153481169603661887282968021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204641559471549183043957361 153481169603661887282968021)
                    ·
                      refine ⟨3597214912585825483194563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153481169603661887282968021 3597214912585825483194563)
                      ·
                        rfl

theorem cell23_7005551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_7005551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005551 prefixEnd_7005551 := by exact prefixLift 7005551
  have htrace : WordTrace (prefixWord ++ tailWord_7005551) baseStart_7005551 baseEnd_7005551 := by
    simpa [prefixWord, tailWord_7005551, baseEnd_7005551] using wordTrace_append hprefix tailTrace_7005551
  have hstable : (prefixWord ++ tailWord_7005551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005551).length < 2 ^ (prefixWord ++ tailWord_7005551).sum := by decide
  have hdescent : baseEnd_7005551 < baseStart_7005551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005552 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 2, 2, 2]
def baseStart_7005552 : Nat := 118140960795 + 7005552 * 2 ^ 59
def prefixEnd_7005552 : Nat := 4983230072969 + 3 ^ 40 * 7005552 * 2
def baseEnd_7005552 : Nat := 3597215426066479979282059

theorem tailTrace_7005552 : CollatzResearch.WordTrace tailWord_7005552 prefixEnd_7005552 3597215426066479979282059 := by
  unfold tailWord_7005552
  simp only [CollatzResearch.WordTrace]
  refine ⟨127756736358044515936109455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170342315144059354581479273 127756736358044515936109455)
  ·
    refine ⟨191635104537066773904164183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127756736358044515936109455 191635104537066773904164183)
    ·
      refine ⟨287452656805600160856246275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191635104537066773904164183 287452656805600160856246275)
      ·
        refine ⟨431178985208400241284369413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287452656805600160856246275 431178985208400241284369413)
        ·
          refine ⟨80846059726575045240819265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431178985208400241284369413 80846059726575045240819265)
          ·
            refine ⟨60634544794931283930614449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80846059726575045240819265 60634544794931283930614449)
            ·
              refine ⟨45475908596198462947960837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60634544794931283930614449 45475908596198462947960837)
              ·
                refine ⟨8526732861787211802742657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45475908596198462947960837 8526732861787211802742657)
                ·
                  refine ⟨6395049646340408852056993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8526732861787211802742657 6395049646340408852056993)
                  ·
                    refine ⟨4796287234755306639042745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6395049646340408852056993 4796287234755306639042745)
                    ·
                      refine ⟨3597215426066479979282059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796287234755306639042745 3597215426066479979282059)
                      ·
                        rfl

theorem cell23_7005552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 2, 2].length) (baseStart_7005552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005552 prefixEnd_7005552 := by exact prefixLift 7005552
  have htrace : WordTrace (prefixWord ++ tailWord_7005552) baseStart_7005552 baseEnd_7005552 := by
    simpa [prefixWord, tailWord_7005552, baseEnd_7005552] using wordTrace_append hprefix tailTrace_7005552
  have hstable : (prefixWord ++ tailWord_7005552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005552).length < 2 ^ (prefixWord ++ tailWord_7005552).sum := by decide
  have hdescent : baseEnd_7005552 < baseStart_7005552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005568 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 3]
def baseStart_7005568 : Nat := 118140960795 + 7005568 * 2 ^ 59
def prefixEnd_7005568 : Nat := 4983230072969 + 3 ^ 40 * 7005568 * 2
def baseEnd_7005568 : Nat := 3597223641756951916681985

theorem tailTrace_7005568 : CollatzResearch.WordTrace tailWord_7005568 prefixEnd_7005568 3597223641756951916681985 := by
  unfold tailWord_7005568
  simp only [CollatzResearch.WordTrace]
  refine ⟨127757028142015533302400679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170342704189354044403200905 127757028142015533302400679)
  ·
    refine ⟨191635542213023299953601019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127757028142015533302400679 191635542213023299953601019)
    ·
      refine ⟨287453313319534949930401529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191635542213023299953601019 287453313319534949930401529)
      ·
        refine ⟨215589984989651212447801147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287453313319534949930401529 215589984989651212447801147)
        ·
          refine ⟨323384977484476818671701721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215589984989651212447801147 323384977484476818671701721)
          ·
            refine ⟨242538733113357614003776291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323384977484476818671701721 242538733113357614003776291)
            ·
              refine ⟨363808099670036421005664437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242538733113357614003776291 363808099670036421005664437)
              ·
                refine ⟨34107009344065914469281041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 363808099670036421005664437 34107009344065914469281041)
                ·
                  refine ⟨25580257008049435851960781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34107009344065914469281041 25580257008049435851960781)
                  ·
                    refine ⟨9592596378018538444485293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25580257008049435851960781 9592596378018538444485293)
                    ·
                      refine ⟨3597223641756951916681985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9592596378018538444485293 3597223641756951916681985)
                      ·
                        rfl

theorem cell23_7005568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_7005568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005568 prefixEnd_7005568 := by exact prefixLift 7005568
  have htrace : WordTrace (prefixWord ++ tailWord_7005568) baseStart_7005568 baseEnd_7005568 := by
    simpa [prefixWord, tailWord_7005568, baseEnd_7005568] using wordTrace_append hprefix tailTrace_7005568
  have hstable : (prefixWord ++ tailWord_7005568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005568).length < 2 ^ (prefixWord ++ tailWord_7005568).sum := by decide
  have hdescent : baseEnd_7005568 < baseStart_7005568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005642 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_7005642 : Nat := 118140960795 + 7005642 * 2 ^ 59
def prefixEnd_7005642 : Nat := 4983230072969 + 3 ^ 40 * 7005642 * 2
def baseEnd_7005642 : Nat := 3597261639325384627156645

theorem tailTrace_7005642 : CollatzResearch.WordTrace tailWord_7005642 prefixEnd_7005642 3597261639325384627156645 := by
  unfold tailWord_7005642
  simp only [CollatzResearch.WordTrace]
  refine ⟨63879188821440744310748795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170344503523841984828663453 63879188821440744310748795)
  ·
    refine ⟨95818783232161116466123193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63879188821440744310748795 95818783232161116466123193)
    ·
      refine ⟨71864087424120837349592395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95818783232161116466123193 71864087424120837349592395)
      ·
        refine ⟨107796131136181256024388593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71864087424120837349592395 107796131136181256024388593)
        ·
          refine ⟨80847098352135942018291445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107796131136181256024388593 80847098352135942018291445)
          ·
            refine ⟨7579415470512744564214823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80847098352135942018291445 7579415470512744564214823)
            ·
              refine ⟨11369123205769116846322235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7579415470512744564214823 11369123205769116846322235)
              ·
                refine ⟨17053684808653675269483353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11369123205769116846322235 17053684808653675269483353)
                ·
                  refine ⟨12790263606490256452112515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17053684808653675269483353 12790263606490256452112515)
                  ·
                    refine ⟨19185395409735384678168773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12790263606490256452112515 19185395409735384678168773)
                    ·
                      refine ⟨3597261639325384627156645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19185395409735384678168773 3597261639325384627156645)
                      ·
                        rfl

theorem cell23_7005642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_7005642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005642 prefixEnd_7005642 := by exact prefixLift 7005642
  have htrace : WordTrace (prefixWord ++ tailWord_7005642) baseStart_7005642 baseEnd_7005642 := by
    simpa [prefixWord, tailWord_7005642, baseEnd_7005642] using wordTrace_append hprefix tailTrace_7005642
  have hstable : (prefixWord ++ tailWord_7005642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005642).length < 2 ^ (prefixWord ++ tailWord_7005642).sum := by decide
  have hdescent : baseEnd_7005642 < baseStart_7005642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005665 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 6]
def baseStart_7005665 : Nat := 118140960795 + 7005665 * 2 ^ 59
def prefixEnd_7005665 : Nat := 4983230072969 + 3 ^ 40 * 7005665 * 2
def baseEnd_7005665 : Nat := 399697049931159781907671

theorem tailTrace_7005665 : CollatzResearch.WordTrace tailWord_7005665 prefixEnd_7005665 399697049931159781907671 := by
  unfold tailWord_7005665
  simp only [CollatzResearch.WordTrace]
  refine ⟨255517594164679652171082449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170345062776453101447388299 255517594164679652171082449)
  ·
    refine ⟨191638195623509739128311837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255517594164679652171082449 191638195623509739128311837)
    ·
      refine ⟨71864323358816152173116939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191638195623509739128311837 71864323358816152173116939)
      ·
        refine ⟨107796485038224228259675409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71864323358816152173116939 107796485038224228259675409)
        ·
          refine ⟨80847363778668171194756557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107796485038224228259675409 80847363778668171194756557)
          ·
            refine ⟨30317761417000564198033709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80847363778668171194756557 30317761417000564198033709)
            ·
              refine ⟨11369160531375211574262641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30317761417000564198033709 11369160531375211574262641)
              ·
                refine ⟨8526870398531408680696981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11369160531375211574262641 8526870398531408680696981)
                ·
                  refine ⟨399697049931159781907671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8526870398531408680696981 399697049931159781907671)
                  ·
                    rfl

theorem cell23_7005665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 6].length) (baseStart_7005665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005665 prefixEnd_7005665 := by exact prefixLift 7005665
  have htrace : WordTrace (prefixWord ++ tailWord_7005665) baseStart_7005665 baseEnd_7005665 := by
    simpa [prefixWord, tailWord_7005665, baseEnd_7005665] using wordTrace_append hprefix tailTrace_7005665
  have hstable : (prefixWord ++ tailWord_7005665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005665).length < 2 ^ (prefixWord ++ tailWord_7005665).sum := by decide
  have hdescent : baseEnd_7005665 < baseStart_7005665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005669 : List Nat := [1, 3, 1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_7005669 : Nat := 118140960795 + 7005669 * 2 ^ 59
def prefixEnd_7005669 : Nat := 4983230072969 + 3 ^ 40 * 7005669 * 2
def baseEnd_7005669 : Nat := 1199091834434352007173007

theorem tailTrace_7005669 : CollatzResearch.WordTrace tailWord_7005669 prefixEnd_7005669 1199091834434352007173007 := by
  unfold tailWord_7005669
  simp only [CollatzResearch.WordTrace]
  refine ⟨255517740056665160854228061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170345160037776773902818707 255517740056665160854228061)
  ·
    refine ⟨95819152521249435320335523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255517740056665160854228061 95819152521249435320335523)
    ·
      refine ⟨143728728781874152980503285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95819152521249435320335523 143728728781874152980503285)
      ·
        refine ⟨13474568323300701841922183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143728728781874152980503285 13474568323300701841922183)
        ·
          refine ⟨20211852484951052762883275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13474568323300701841922183 20211852484951052762883275)
          ·
            refine ⟨30317778727426579144324913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20211852484951052762883275 30317778727426579144324913)
            ·
              refine ⟨22738334045569934358243685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30317778727426579144324913 22738334045569934358243685)
              ·
                refine ⟨4263437633544362692170691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22738334045569934358243685 4263437633544362692170691)
                ·
                  refine ⟨6395156450316544038256037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263437633544362692170691 6395156450316544038256037)
                  ·
                    refine ⟨1199091834434352007173007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6395156450316544038256037 1199091834434352007173007)
                    ·
                      rfl

theorem cell23_7005669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_7005669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005669 prefixEnd_7005669 := by exact prefixLift 7005669
  have htrace : WordTrace (prefixWord ++ tailWord_7005669) baseStart_7005669 baseEnd_7005669 := by
    simpa [prefixWord, tailWord_7005669, baseEnd_7005669] using wordTrace_append hprefix tailTrace_7005669
  have hstable : (prefixWord ++ tailWord_7005669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005669).length < 2 ^ (prefixWord ++ tailWord_7005669).sum := by decide
  have hdescent : baseEnd_7005669 < baseStart_7005669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005692 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_7005692 : Nat := 118140960795 + 7005692 * 2 ^ 59
def prefixEnd_7005692 : Nat := 4983230072969 + 3 ^ 40 * 7005692 * 2
def baseEnd_7005692 : Nat := 3597287313358109431531415

theorem tailTrace_7005692 : CollatzResearch.WordTrace tailWord_7005692 prefixEnd_7005692 3597287313358109431531415 := by
  unfold tailWord_7005692
  simp only [CollatzResearch.WordTrace]
  refine ⟨127759289467790917891157665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170345719290387890521543553 127759289467790917891157665)
  ·
    refine ⟨95819467100843188418368249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127759289467790917891157665 95819467100843188418368249)
    ·
      refine ⟨71864600325632391313776187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95819467100843188418368249 71864600325632391313776187)
      ·
        refine ⟨107796900488448586970664281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71864600325632391313776187 107796900488448586970664281)
        ·
          refine ⟨80847675366336440227998211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107796900488448586970664281 80847675366336440227998211)
          ·
            refine ⟨121271513049504660341997317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80847675366336440227998211 121271513049504660341997317)
            ·
              refine ⟨22738408696782123814124497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121271513049504660341997317 22738408696782123814124497)
              ·
                refine ⟨17053806522586592860593373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22738408696782123814124497 17053806522586592860593373)
                ·
                  refine ⟨6395177445969972322722515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17053806522586592860593373 6395177445969972322722515)
                  ·
                    refine ⟨9592766168954958484083773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6395177445969972322722515 9592766168954958484083773)
                    ·
                      refine ⟨3597287313358109431531415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9592766168954958484083773 3597287313358109431531415)
                      ·
                        rfl

theorem cell23_7005692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_7005692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005692 prefixEnd_7005692 := by exact prefixLift 7005692
  have htrace : WordTrace (prefixWord ++ tailWord_7005692) baseStart_7005692 baseEnd_7005692 := by
    simpa [prefixWord, tailWord_7005692, baseEnd_7005692] using wordTrace_append hprefix tailTrace_7005692
  have hstable : (prefixWord ++ tailWord_7005692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005692).length < 2 ^ (prefixWord ++ tailWord_7005692).sum := by decide
  have hdescent : baseEnd_7005692 < baseStart_7005692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005745 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_7005745 : Nat := 118140960795 + 7005745 * 2 ^ 59
def prefixEnd_7005745 : Nat := 4983230072969 + 3 ^ 40 * 7005745 * 2
def baseEnd_7005745 : Nat := 3597314527832797724168671

theorem tailTrace_7005745 : CollatzResearch.WordTrace tailWord_7005745 prefixEnd_7005745 3597314527832797724168671 := by
  unfold tailWord_7005745
  simp only [CollatzResearch.WordTrace]
  refine ⟨255520512004389825833994689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170347008002926550555996459 255520512004389825833994689)
  ·
    refine ⟨191640384003292369375496017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255520512004389825833994689 191640384003292369375496017)
    ·
      refine ⟨143730288002469277031622013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191640384003292369375496017 143730288002469277031622013)
      ·
        refine ⟨53898858000925978886858255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143730288002469277031622013 53898858000925978886858255)
        ·
          refine ⟨80848287001388968330287383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53898858000925978886858255 80848287001388968330287383)
          ·
            refine ⟨121272430502083452495431075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80848287001388968330287383 121272430502083452495431075)
            ·
              refine ⟨181908645753125178743146613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121272430502083452495431075 181908645753125178743146613)
              ·
                refine ⟨17053935539355485507169995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181908645753125178743146613 17053935539355485507169995)
                ·
                  refine ⟨25580903309033228260754993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17053935539355485507169995 25580903309033228260754993)
                  ·
                    refine ⟨19185677481774921195566245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25580903309033228260754993 19185677481774921195566245)
                    ·
                      refine ⟨3597314527832797724168671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19185677481774921195566245 3597314527832797724168671)
                      ·
                        rfl

theorem cell23_7005745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_7005745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005745 prefixEnd_7005745 := by exact prefixLift 7005745
  have htrace : WordTrace (prefixWord ++ tailWord_7005745) baseStart_7005745 baseEnd_7005745 := by
    simpa [prefixWord, tailWord_7005745, baseEnd_7005745] using wordTrace_append hprefix tailTrace_7005745
  have hstable : (prefixWord ++ tailWord_7005745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005745).length < 2 ^ (prefixWord ++ tailWord_7005745).sum := by decide
  have hdescent : baseEnd_7005745 < baseStart_7005745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005749 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_7005749 : Nat := 118140960795 + 7005749 * 2 ^ 59
def prefixEnd_7005749 : Nat := 4983230072969 + 3 ^ 40 * 7005749 * 2
def baseEnd_7005749 : Nat := 3597316581755415708518653

theorem tailTrace_7005749 : CollatzResearch.WordTrace tailWord_7005749 prefixEnd_7005749 3597316581755415708518653 := by
  unfold tailWord_7005749
  simp only [CollatzResearch.WordTrace]
  refine ⟨255520657896375334517140301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170347105264250223011426867 255520657896375334517140301)
  ·
    refine ⟨95820246711140750443927613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255520657896375334517140301 95820246711140750443927613)
    ·
      refine ⟨35932592516677781416472855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95820246711140750443927613 35932592516677781416472855)
      ·
        refine ⟨53898888775016672124709283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35932592516677781416472855 53898888775016672124709283)
        ·
          refine ⟨80848333162525008187063925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53898888775016672124709283 80848333162525008187063925)
          ·
            refine ⟨7579531233986719517537243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80848333162525008187063925 7579531233986719517537243)
            ·
              refine ⟨11369296850980079276305865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7579531233986719517537243 11369296850980079276305865)
              ·
                refine ⟨8526972638235059457229399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11369296850980079276305865 8526972638235059457229399)
                ·
                  refine ⟨12790458957352589185844099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8526972638235059457229399 12790458957352589185844099)
                  ·
                    refine ⟨19185688436028883778766149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12790458957352589185844099 19185688436028883778766149)
                    ·
                      refine ⟨3597316581755415708518653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19185688436028883778766149 3597316581755415708518653)
                      ·
                        rfl

theorem cell23_7005749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_7005749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005749 prefixEnd_7005749 := by exact prefixLift 7005749
  have htrace : WordTrace (prefixWord ++ tailWord_7005749) baseStart_7005749 baseEnd_7005749 := by
    simpa [prefixWord, tailWord_7005749, baseEnd_7005749] using wordTrace_append hprefix tailTrace_7005749
  have hstable : (prefixWord ++ tailWord_7005749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005749).length < 2 ^ (prefixWord ++ tailWord_7005749).sum := by decide
  have hdescent : baseEnd_7005749 < baseStart_7005749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005752 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_7005752 : Nat := 118140960795 + 7005752 * 2 ^ 59
def prefixEnd_7005752 : Nat := 4983230072969 + 3 ^ 40 * 7005752 * 2
def baseEnd_7005752 : Nat := 3597318122197379196781139

theorem tailTrace_7005752 : CollatzResearch.WordTrace tailWord_7005752 prefixEnd_7005752 3597318122197379196781139 := by
  unfold tailWord_7005752
  simp only [CollatzResearch.WordTrace]
  refine ⟨127760383657682233014749755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170347178210242977352999673 127760383657682233014749755)
  ·
    refine ⟨191640575486523349522124633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127760383657682233014749755 191640575486523349522124633)
    ·
      refine ⟨143730431614892512141593475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191640575486523349522124633 143730431614892512141593475)
      ·
        refine ⟨215595647422338768212390213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143730431614892512141593475 215595647422338768212390213)
        ·
          refine ⟨40424183891688519039823165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215595647422338768212390213 40424183891688519039823165)
          ·
            refine ⟨15159068959383194639933687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40424183891688519039823165 15159068959383194639933687)
            ·
              refine ⟨22738603439074791959900531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15159068959383194639933687 22738603439074791959900531)
              ·
                refine ⟨34107905158612187939850797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22738603439074791959900531 34107905158612187939850797)
                ·
                  refine ⟨12790464434479570477444049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34107905158612187939850797 12790464434479570477444049)
                  ·
                    refine ⟨9592848325859677858083037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12790464434479570477444049 9592848325859677858083037)
                    ·
                      refine ⟨3597318122197379196781139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9592848325859677858083037 3597318122197379196781139)
                      ·
                        rfl

theorem cell23_7005752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_7005752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005752 prefixEnd_7005752 := by exact prefixLift 7005752
  have htrace : WordTrace (prefixWord ++ tailWord_7005752) baseStart_7005752 baseEnd_7005752 := by
    simpa [prefixWord, tailWord_7005752, baseEnd_7005752] using wordTrace_append hprefix tailTrace_7005752
  have hstable : (prefixWord ++ tailWord_7005752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005752).length < 2 ^ (prefixWord ++ tailWord_7005752).sum := by decide
  have hdescent : baseEnd_7005752 < baseStart_7005752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005783 : List Nat := [1, 1, 3, 2, 2, 3, 4, 2, 1, 2, 2]
def baseStart_7005783 : Nat := 118140960795 + 7005783 * 2 ^ 59
def prefixEnd_7005783 : Nat := 4983230072969 + 3 ^ 40 * 7005783 * 2
def baseEnd_7005783 : Nat := 3597334040097668575493497

theorem tailTrace_7005783 : CollatzResearch.WordTrace tailWord_7005783 prefixEnd_7005783 3597334040097668575493497 := by
  unfold tailWord_7005783
  simp only [CollatzResearch.WordTrace]
  refine ⟨255521897978252158323878003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170347931985501438882585335 255521897978252158323878003)
  ·
    refine ⟨383282846967378237485817005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255521897978252158323878003 383282846967378237485817005)
    ·
      refine ⟨143731067612766839057181377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383282846967378237485817005 143731067612766839057181377)
      ·
        refine ⟨107798300709575129292886033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143731067612766839057181377 107798300709575129292886033)
        ·
          refine ⟨80848725532181346969664525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107798300709575129292886033 80848725532181346969664525)
          ·
            refine ⟨30318272074568005113624197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80848725532181346969664525 30318272074568005113624197)
            ·
              refine ⟨5684676013981500958804537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30318272074568005113624197 5684676013981500958804537)
              ·
                refine ⟨4263507010486125719103403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5684676013981500958804537 4263507010486125719103403)
                ·
                  refine ⟨6395260515729188578655105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263507010486125719103403 6395260515729188578655105)
                  ·
                    refine ⟨4796445386796891433991329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6395260515729188578655105 4796445386796891433991329)
                    ·
                      refine ⟨3597334040097668575493497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796445386796891433991329 3597334040097668575493497)
                      ·
                        rfl

theorem cell23_7005783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_7005783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005783 prefixEnd_7005783 := by exact prefixLift 7005783
  have htrace : WordTrace (prefixWord ++ tailWord_7005783) baseStart_7005783 baseEnd_7005783 := by
    simpa [prefixWord, tailWord_7005783, baseEnd_7005783] using wordTrace_append hprefix tailTrace_7005783
  have hstable : (prefixWord ++ tailWord_7005783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005783).length < 2 ^ (prefixWord ++ tailWord_7005783).sum := by decide
  have hdescent : baseEnd_7005783 < baseStart_7005783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005799 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_7005799 : Nat := 118140960795 + 7005799 * 2 ^ 59
def prefixEnd_7005799 : Nat := 4983230072969 + 3 ^ 40 * 7005799 * 2
def baseEnd_7005799 : Nat := 3597342255788140512893423

theorem tailTrace_7005799 : CollatzResearch.WordTrace tailWord_7005799 prefixEnd_7005799 3597342255788140512893423 := by
  unfold tailWord_7005799
  simp only [CollatzResearch.WordTrace]
  refine ⟨255522481546194193056460451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170348321030796128704306967 255522481546194193056460451)
  ·
    refine ⟨383283722319291289584690677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255522481546194193056460451 383283722319291289584690677)
    ·
      refine ⟨35932848967433558398564751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 383283722319291289584690677 35932848967433558398564751)
      ·
        refine ⟨53899273451150337597847127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35932848967433558398564751 53899273451150337597847127)
        ·
          refine ⟨80848910176725506396770691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53899273451150337597847127 80848910176725506396770691)
          ·
            refine ⟨121273365265088259595156037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80848910176725506396770691 121273365265088259595156037)
            ·
              refine ⟨22738755987204048674091757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121273365265088259595156037 22738755987204048674091757)
              ·
                refine ⟨8527033495201518252784409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22738755987204048674091757 8527033495201518252784409)
                ·
                  refine ⟨6395275121401138689588307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8527033495201518252784409 6395275121401138689588307)
                  ·
                    refine ⟨9592912682101708034382461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6395275121401138689588307 9592912682101708034382461)
                    ·
                      refine ⟨3597342255788140512893423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9592912682101708034382461 3597342255788140512893423)
                      ·
                        rfl

theorem cell23_7005799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_7005799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005799 prefixEnd_7005799 := by exact prefixLift 7005799
  have htrace : WordTrace (prefixWord ++ tailWord_7005799) baseStart_7005799 baseEnd_7005799 := by
    simpa [prefixWord, tailWord_7005799, baseEnd_7005799] using wordTrace_append hprefix tailTrace_7005799
  have hstable : (prefixWord ++ tailWord_7005799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005799).length < 2 ^ (prefixWord ++ tailWord_7005799).sum := by decide
  have hdescent : baseEnd_7005799 < baseStart_7005799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005835 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 4]
def baseStart_7005835 : Nat := 118140960795 + 7005835 * 2 ^ 59
def prefixEnd_7005835 : Nat := 4983230072969 + 3 ^ 40 * 7005835 * 2
def baseEnd_7005835 : Nat := 3597360741091702372043257

theorem tailTrace_7005835 : CollatzResearch.WordTrace tailWord_7005835 prefixEnd_7005835 3597360741091702372043257 := by
  unfold tailWord_7005835
  simp only [CollatzResearch.WordTrace]
  refine ⟨255523794574063771204770959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170349196382709180803180639 255523794574063771204770959)
  ·
    refine ⟨383285691861095656807156439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255523794574063771204770959 383285691861095656807156439)
    ·
      refine ⟨574928537791643485210734659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383285691861095656807156439 574928537791643485210734659)
      ·
        refine ⟨862392806687465227816101989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574928537791643485210734659 862392806687465227816101989)
        ·
          refine ⟨161698651253899730215519123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 862392806687465227816101989 161698651253899730215519123)
          ·
            refine ⟨242547976880849595323278685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161698651253899730215519123 242547976880849595323278685)
            ·
              refine ⟨90955491330318598246229507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242547976880849595323278685 90955491330318598246229507)
              ·
                refine ⟨136433236995477897369344261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90955491330318598246229507 136433236995477897369344261)
                ·
                  refine ⟨25581231936652105756752049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136433236995477897369344261 25581231936652105756752049)
                  ·
                    refine ⟨19185923952489079317564037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25581231936652105756752049 19185923952489079317564037)
                    ·
                      refine ⟨3597360741091702372043257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19185923952489079317564037 3597360741091702372043257)
                      ·
                        rfl

theorem cell23_7005835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 4].length) (baseStart_7005835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005835 prefixEnd_7005835 := by exact prefixLift 7005835
  have htrace : WordTrace (prefixWord ++ tailWord_7005835) baseStart_7005835 baseEnd_7005835 := by
    simpa [prefixWord, tailWord_7005835, baseEnd_7005835] using wordTrace_append hprefix tailTrace_7005835
  have hstable : (prefixWord ++ tailWord_7005835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005835).length < 2 ^ (prefixWord ++ tailWord_7005835).sum := by decide
  have hdescent : baseEnd_7005835 < baseStart_7005835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005856 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 1, 4, 2]
def baseStart_7005856 : Nat := 118140960795 + 7005856 * 2 ^ 59
def prefixEnd_7005856 : Nat := 4983230072969 + 3 ^ 40 * 7005856 * 2
def baseEnd_7005856 : Nat := 3597371524185446789880661

theorem tailTrace_7005856 : CollatzResearch.WordTrace tailWord_7005856 prefixEnd_7005856 3597371524185446789880661 := by
  unfold tailWord_7005856
  simp only [CollatzResearch.WordTrace]
  refine ⟨127762280253493845895642711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170349707004658461194190281 127762280253493845895642711)
  ·
    refine ⟨191643420380240768843464067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127762280253493845895642711 191643420380240768843464067)
    ·
      refine ⟨287465130570361153265196101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191643420380240768843464067 287465130570361153265196101)
      ·
        refine ⟨53899711981942716237224269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287465130570361153265196101 53899711981942716237224269)
        ·
          refine ⟨20212391993228518588959101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53899711981942716237224269 20212391993228518588959101)
          ·
            refine ⟨7579646997460694470859663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20212391993228518588959101 7579646997460694470859663)
            ·
              refine ⟨11369470496191041706289495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7579646997460694470859663 11369470496191041706289495)
              ·
                refine ⟨17054205744286562559434243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11369470496191041706289495 17054205744286562559434243)
                ·
                  refine ⟨25581308616429843839151365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17054205744286562559434243 25581308616429843839151365)
                  ·
                    refine ⟨4796495365580595719840881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25581308616429843839151365 4796495365580595719840881)
                    ·
                      refine ⟨3597371524185446789880661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796495365580595719840881 3597371524185446789880661)
                      ·
                        rfl

theorem cell23_7005856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_7005856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005856 prefixEnd_7005856 := by exact prefixLift 7005856
  have htrace : WordTrace (prefixWord ++ tailWord_7005856) baseStart_7005856 baseEnd_7005856 := by
    simpa [prefixWord, tailWord_7005856, baseEnd_7005856] using wordTrace_append hprefix tailTrace_7005856
  have hstable : (prefixWord ++ tailWord_7005856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005856).length < 2 ^ (prefixWord ++ tailWord_7005856).sum := by decide
  have hdescent : baseEnd_7005856 < baseStart_7005856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005875 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 1, 7]
def baseStart_7005875 : Nat := 118140960795 + 7005875 * 2 ^ 59
def prefixEnd_7005875 : Nat := 4983230072969 + 3 ^ 40 * 7005875 * 2
def baseEnd_7005875 : Nat := 1199127093439294071847691

theorem tailTrace_7005875 : CollatzResearch.WordTrace tailWord_7005875 prefixEnd_7005875 1199127093439294071847691 := by
  unfold tailWord_7005875
  simp only [CollatzResearch.WordTrace]
  refine ⟨255525253493918858036227079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170350168995945905357484719 255525253493918858036227079)
  ·
    refine ⟨383287880240878287054340619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255525253493918858036227079 383287880240878287054340619)
    ·
      refine ⟨574931820361317430581510929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383287880240878287054340619 574931820361317430581510929)
      ·
        refine ⟨431198865270988072936133197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574931820361317430581510929 431198865270988072936133197)
        ·
          refine ⟨161699574476620527351049949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431198865270988072936133197 161699574476620527351049949)
          ·
            refine ⟨60637340428732697756643731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161699574476620527351049949 60637340428732697756643731)
            ·
              refine ⟨90956010643099046634965597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60637340428732697756643731 90956010643099046634965597)
              ·
                refine ⟨34108503991162142488112099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90956010643099046634965597 34108503991162142488112099)
                ·
                  refine ⟨51162755986743213732168149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34108503991162142488112099 51162755986743213732168149)
                  ·
                    refine ⟨1199127093439294071847691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51162755986743213732168149 1199127093439294071847691)
                    ·
                      rfl

theorem cell23_7005875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 7].length) (baseStart_7005875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005875 prefixEnd_7005875 := by exact prefixLift 7005875
  have htrace : WordTrace (prefixWord ++ tailWord_7005875) baseStart_7005875 baseEnd_7005875 := by
    simpa [prefixWord, tailWord_7005875, baseEnd_7005875] using wordTrace_append hprefix tailTrace_7005875
  have hstable : (prefixWord ++ tailWord_7005875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005875).length < 2 ^ (prefixWord ++ tailWord_7005875).sum := by decide
  have hdescent : baseEnd_7005875 < baseStart_7005875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005879 : List Nat := [1, 1, 3, 1, 5, 1, 3, 3, 5]
def baseStart_7005879 : Nat := 118140960795 + 7005879 * 2 ^ 59
def prefixEnd_7005879 : Nat := 4983230072969 + 3 ^ 40 * 7005879 * 2
def baseEnd_7005879 : Nat := 399709259360055577765895

theorem tailTrace_7005879 : CollatzResearch.WordTrace tailWord_7005879 prefixEnd_7005879 399709259360055577765895 := by
  unfold tailWord_7005879
  simp only [CollatzResearch.WordTrace]
  refine ⟨255525399385904366719372691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170350266257269577812915127 255525399385904366719372691)
  ·
    refine ⟨383288099078856550079059037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255525399385904366719372691 383288099078856550079059037)
    ·
      refine ⟨143733037154571206279647139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383288099078856550079059037 143733037154571206279647139)
      ·
        refine ⟨215599555731856809419470709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143733037154571206279647139 215599555731856809419470709)
        ·
          refine ⟨20212458349861575883075379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215599555731856809419470709 20212458349861575883075379)
          ·
            refine ⟨30318687524792363824613069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20212458349861575883075379 30318687524792363824613069)
            ·
              refine ⟨11369507821797136434229901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30318687524792363824613069 11369507821797136434229901)
              ·
                refine ⟨4263565433173926162836213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11369507821797136434229901 4263565433173926162836213)
                ·
                  refine ⟨399709259360055577765895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4263565433173926162836213 399709259360055577765895)
                  ·
                    rfl

theorem cell23_7005879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 5].length) (baseStart_7005879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005879 prefixEnd_7005879 := by exact prefixLift 7005879
  have htrace : WordTrace (prefixWord ++ tailWord_7005879) baseStart_7005879 baseEnd_7005879 := by
    simpa [prefixWord, tailWord_7005879, baseEnd_7005879] using wordTrace_append hprefix tailTrace_7005879
  have hstable : (prefixWord ++ tailWord_7005879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005879).length < 2 ^ (prefixWord ++ tailWord_7005879).sum := by decide
  have hdescent : baseEnd_7005879 < baseStart_7005879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005902 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_7005902 : Nat := 118140960795 + 7005902 * 2 ^ 59
def prefixEnd_7005902 : Nat := 4983230072969 + 3 ^ 40 * 7005902 * 2
def baseEnd_7005902 : Nat := 3597395144295553609905449

theorem tailTrace_7005902 : CollatzResearch.WordTrace tailWord_7005902 prefixEnd_7005902 3597395144295553609905449 := by
  unfold tailWord_7005902
  simp only [CollatzResearch.WordTrace]
  refine ⟨31940779783102630205932495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170350825509880694431639973 31940779783102630205932495)
  ·
    refine ⟨47911169674653945308898743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31940779783102630205932495 47911169674653945308898743)
    ·
      refine ⟨71866754511980917963348115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47911169674653945308898743 71866754511980917963348115)
      ·
        refine ⟨107800131767971376945022173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71866754511980917963348115 107800131767971376945022173)
        ·
          refine ⟨40425049412989266354383315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107800131767971376945022173 40425049412989266354383315)
          ·
            refine ⟨60637574119483899531574973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40425049412989266354383315 60637574119483899531574973)
            ·
              refine ⟨22739090294806462324340615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60637574119483899531574973 22739090294806462324340615)
              ·
                refine ⟨34108635442209693486510923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22739090294806462324340615 34108635442209693486510923)
                ·
                  refine ⟨51162953163314540229766385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34108635442209693486510923 51162953163314540229766385)
                  ·
                    refine ⟨38372214872485905172324789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51162953163314540229766385 38372214872485905172324789)
                    ·
                      refine ⟨3597395144295553609905449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38372214872485905172324789 3597395144295553609905449)
                      ·
                        rfl

theorem cell23_7005902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_7005902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005902 prefixEnd_7005902 := by exact prefixLift 7005902
  have htrace : WordTrace (prefixWord ++ tailWord_7005902) baseStart_7005902 baseEnd_7005902 := by
    simpa [prefixWord, tailWord_7005902, baseEnd_7005902] using wordTrace_append hprefix tailTrace_7005902
  have hstable : (prefixWord ++ tailWord_7005902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005902).length < 2 ^ (prefixWord ++ tailWord_7005902).sum := by decide
  have hdescent : baseEnd_7005902 < baseStart_7005902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005912 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_7005912 : Nat := 118140960795 + 7005912 * 2 ^ 59
def prefixEnd_7005912 : Nat := 4983230072969 + 3 ^ 40 * 7005912 * 2
def baseEnd_7005912 : Nat := 3597400279102098570780403

theorem tailTrace_7005912 : CollatzResearch.WordTrace tailWord_7005912 prefixEnd_7005912 3597400279102098570780403 := by
  unfold tailWord_7005912
  simp only [CollatzResearch.WordTrace]
  refine ⟨127763301497392406677661995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170351068663189875570215993 127763301497392406677661995)
  ·
    refine ⟨191644952246088610016492993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127763301497392406677661995 191644952246088610016492993)
    ·
      refine ⟨143733714184566457512369745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191644952246088610016492993 143733714184566457512369745)
      ·
        refine ⟨107800285638424843134277309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143733714184566457512369745 107800285638424843134277309)
        ·
          refine ⟨40425107114409316175353991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107800285638424843134277309 40425107114409316175353991)
          ·
            refine ⟨60637660671613974263030987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40425107114409316175353991 60637660671613974263030987)
            ·
              refine ⟨90956491007420961394546481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60637660671613974263030987 90956491007420961394546481)
              ·
                refine ⟨68217368255565721045909861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90956491007420961394546481 68217368255565721045909861)
                ·
                  refine ⟨12790756547918572696108099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68217368255565721045909861 12790756547918572696108099)
                  ·
                    refine ⟨19186134821877859044162149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12790756547918572696108099 19186134821877859044162149)
                    ·
                      refine ⟨3597400279102098570780403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19186134821877859044162149 3597400279102098570780403)
                      ·
                        rfl

theorem cell23_7005912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_7005912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005912 prefixEnd_7005912 := by exact prefixLift 7005912
  have htrace : WordTrace (prefixWord ++ tailWord_7005912) baseStart_7005912 baseEnd_7005912 := by
    simpa [prefixWord, tailWord_7005912, baseEnd_7005912] using wordTrace_append hprefix tailTrace_7005912
  have hstable : (prefixWord ++ tailWord_7005912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005912).length < 2 ^ (prefixWord ++ tailWord_7005912).sum := by decide
  have hdescent : baseEnd_7005912 < baseStart_7005912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005932 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_7005932 : Nat := 118140960795 + 7005932 * 2 ^ 59
def prefixEnd_7005932 : Nat := 4983230072969 + 3 ^ 40 * 7005932 * 2
def baseEnd_7005932 : Nat := 3597410548715188492530311

theorem tailTrace_7005932 : CollatzResearch.WordTrace tailWord_7005932 prefixEnd_7005932 3597410548715188492530311 := by
  unfold tailWord_7005932
  simp only [CollatzResearch.WordTrace]
  refine ⟨127763666227356178385526025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170351554969808237847368033 127763666227356178385526025)
  ·
    refine ⟨95822749670517133789144519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127763666227356178385526025 95822749670517133789144519)
    ·
      refine ⟨143734124505775700683716779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95822749670517133789144519 143734124505775700683716779)
      ·
        refine ⟨215601186758663551025575169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143734124505775700683716779 215601186758663551025575169)
        ·
          refine ⟨161700890068997663269181377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215601186758663551025575169 161700890068997663269181377)
          ·
            refine ⟨121275667551748247451886033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161700890068997663269181377 121275667551748247451886033)
            ·
              refine ⟨90956750663811185588914525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121275667551748247451886033 90956750663811185588914525)
              ·
                refine ⟨34108781498929194595842947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90956750663811185588914525 34108781498929194595842947)
                ·
                  refine ⟨51163172248393791893764421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34108781498929194595842947 51163172248393791893764421)
                  ·
                    refine ⟨9593094796573835980080829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51163172248393791893764421 9593094796573835980080829)
                    ·
                      refine ⟨3597410548715188492530311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9593094796573835980080829 3597410548715188492530311)
                      ·
                        rfl

theorem cell23_7005932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_7005932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005932 prefixEnd_7005932 := by exact prefixLift 7005932
  have htrace : WordTrace (prefixWord ++ tailWord_7005932) baseStart_7005932 baseEnd_7005932 := by
    simpa [prefixWord, tailWord_7005932, baseEnd_7005932] using wordTrace_append hprefix tailTrace_7005932
  have hstable : (prefixWord ++ tailWord_7005932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005932).length < 2 ^ (prefixWord ++ tailWord_7005932).sum := by decide
  have hdescent : baseEnd_7005932 < baseStart_7005932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7005979 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 3]
def baseStart_7005979 : Nat := 118140960795 + 7005979 * 2 ^ 59
def prefixEnd_7005979 : Nat := 4983230072969 + 3 ^ 40 * 7005979 * 2
def baseEnd_7005979 : Nat := 3597434682305949808642595

theorem tailTrace_7005979 : CollatzResearch.WordTrace tailWord_7005979 prefixEnd_7005979 3597434682305949808642595 := by
  unfold tailWord_7005979
  simp only [CollatzResearch.WordTrace]
  refine ⟨255529046685542083798012991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170352697790361389198675327 255529046685542083798012991)
  ·
    refine ⟨383293570028313125697019487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255529046685542083798012991 383293570028313125697019487)
    ·
      refine ⟨574940355042469688545529231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383293570028313125697019487 574940355042469688545529231)
      ·
        refine ⟨862410532563704532818293847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574940355042469688545529231 862410532563704532818293847)
        ·
          refine ⟨1293615798845556799227440771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862410532563704532818293847 1293615798845556799227440771)
          ·
            refine ⟨1940423698268335198841161157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293615798845556799227440771 1940423698268335198841161157)
            ·
              refine ⟨363829443425312849782717717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1940423698268335198841161157 363829443425312849782717717)
              ·
                refine ⟨17054505160561539833564893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 363829443425312849782717717 17054505160561539833564893)
                ·
                  refine ⟨6395439435210577437586835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17054505160561539833564893 6395439435210577437586835)
                  ·
                    refine ⟨9593159152815866156380253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6395439435210577437586835 9593159152815866156380253)
                    ·
                      refine ⟨3597434682305949808642595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9593159152815866156380253 3597434682305949808642595)
                      ·
                        rfl

theorem cell23_7005979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 3].length) (baseStart_7005979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7005979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7005979 prefixEnd_7005979 := by exact prefixLift 7005979
  have htrace : WordTrace (prefixWord ++ tailWord_7005979) baseStart_7005979 baseEnd_7005979 := by
    simpa [prefixWord, tailWord_7005979, baseEnd_7005979] using wordTrace_append hprefix tailTrace_7005979
  have hstable : (prefixWord ++ tailWord_7005979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7005979).length < 2 ^ (prefixWord ++ tailWord_7005979).sum := by decide
  have hdescent : baseEnd_7005979 < baseStart_7005979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7005979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006012 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_7006012 : Nat := 118140960795 + 7006012 * 2 ^ 59
def prefixEnd_7006012 : Nat := 4983230072969 + 3 ^ 40 * 7006012 * 2
def baseEnd_7006012 : Nat := 1199150542389182726509981

theorem tailTrace_7006012 : CollatzResearch.WordTrace tailWord_7006012 prefixEnd_7006012 1199150542389182726509981 := by
  unfold tailWord_7006012
  simp only [CollatzResearch.WordTrace]
  refine ⟨127765125147211265216982145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170353500196281686955976193 127765125147211265216982145)
  ·
    refine ⟨95823843860408448912736609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127765125147211265216982145 95823843860408448912736609)
    ·
      refine ⟨71867882895306336684552457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95823843860408448912736609 71867882895306336684552457)
      ·
        refine ⟨53900912171479752513414343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71867882895306336684552457 53900912171479752513414343)
        ·
          refine ⟨80851368257219628770121515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53900912171479752513414343 80851368257219628770121515)
          ·
            refine ⟨121277052385829443155182273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80851368257219628770121515 121277052385829443155182273)
            ·
              refine ⟨90957789289372082366386705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121277052385829443155182273 90957789289372082366386705)
              ·
                refine ⟨68218341967029061774790029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90957789289372082366386705 68218341967029061774790029)
                ·
                  refine ⟨25581878237635898165546261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68218341967029061774790029 25581878237635898165546261)
                  ·
                    refine ⟨1199150542389182726509981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25581878237635898165546261 1199150542389182726509981)
                    ·
                      rfl

theorem cell23_7006012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_7006012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006012 prefixEnd_7006012 := by exact prefixLift 7006012
  have htrace : WordTrace (prefixWord ++ tailWord_7006012) baseStart_7006012 baseEnd_7006012 := by
    simpa [prefixWord, tailWord_7006012, baseEnd_7006012] using wordTrace_append hprefix tailTrace_7006012
  have hstable : (prefixWord ++ tailWord_7006012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006012).length < 2 ^ (prefixWord ++ tailWord_7006012).sum := by decide
  have hdescent : baseEnd_7006012 < baseStart_7006012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006013 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7006013 : Nat := 118140960795 + 7006013 * 2 ^ 59
def prefixEnd_7006013 : Nat := 4983230072969 + 3 ^ 40 * 7006013 * 2
def baseEnd_7006013 : Nat := 3597452140648202675617439

theorem tailTrace_7006013 : CollatzResearch.WordTrace tailWord_7006013 prefixEnd_7006013 3597452140648202675617439 := by
  unfold tailWord_7006013
  simp only [CollatzResearch.WordTrace]
  refine ⟨255530286767418907604750693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170353524511612605069833795 255530286767418907604750693)
  ·
    refine ⟨47911928768891045175890755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255530286767418907604750693 47911928768891045175890755)
    ·
      refine ⟨71867893153336567763836133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47911928768891045175890755 71867893153336567763836133)
      ·
        refine ⟨13475229966250606455719275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71867893153336567763836133 13475229966250606455719275)
        ·
          refine ⟨20212844949375909683578913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13475229966250606455719275 20212844949375909683578913)
          ·
            refine ⟨15159633712031932262684185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20212844949375909683578913 15159633712031932262684185)
            ·
              refine ⟨11369725284023949197013139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15159633712031932262684185 11369725284023949197013139)
              ·
                refine ⟨17054587926035923795519709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11369725284023949197013139 17054587926035923795519709)
                ·
                  refine ⟨6395470472263471423319891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17054587926035923795519709 6395470472263471423319891)
                  ·
                    refine ⟨9593205708395207134979837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6395470472263471423319891 9593205708395207134979837)
                    ·
                      refine ⟨3597452140648202675617439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9593205708395207134979837 3597452140648202675617439)
                      ·
                        rfl

theorem cell23_7006013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7006013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006013 prefixEnd_7006013 := by exact prefixLift 7006013
  have htrace : WordTrace (prefixWord ++ tailWord_7006013) baseStart_7006013 baseEnd_7006013 := by
    simpa [prefixWord, tailWord_7006013, baseEnd_7006013] using wordTrace_append hprefix tailTrace_7006013
  have hstable : (prefixWord ++ tailWord_7006013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006013).length < 2 ^ (prefixWord ++ tailWord_7006013).sum := by decide
  have hdescent : baseEnd_7006013 < baseStart_7006013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006036 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_7006036 : Nat := 118140960795 + 7006036 * 2 ^ 59
def prefixEnd_7006036 : Nat := 4983230072969 + 3 ^ 40 * 7006036 * 2
def baseEnd_7006036 : Nat := 3597463950703256085629833

theorem tailTrace_7006036 : CollatzResearch.WordTrace tailWord_7006036 prefixEnd_7006036 3597463950703256085629833 := by
  unfold tailWord_7006036
  simp only [CollatzResearch.WordTrace]
  refine ⟨127765562823167791266418981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170354083764223721688558641 127765562823167791266418981)
  ·
    refine ⟨23956043029343960862453559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127765562823167791266418981 23956043029343960862453559)
    ·
      refine ⟨35934064544015941293680339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23956043029343960862453559 35934064544015941293680339)
      ·
        refine ⟨53901096816023911940520509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35934064544015941293680339 53901096816023911940520509)
        ·
          refine ⟨20212911306008966977695191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53901096816023911940520509 20212911306008966977695191)
          ·
            refine ⟨30319366959013450466542787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20212911306008966977695191 30319366959013450466542787)
            ·
              refine ⟨45479050438520175699814181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30319366959013450466542787 45479050438520175699814181)
              ·
                refine ⟨8527321957222532943715159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45479050438520175699814181 8527321957222532943715159)
                ·
                  refine ⟨12790982935833799415572739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8527321957222532943715159 12790982935833799415572739)
                  ·
                    refine ⟨19186474403750699123359109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12790982935833799415572739 19186474403750699123359109)
                    ·
                      refine ⟨3597463950703256085629833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19186474403750699123359109 3597463950703256085629833)
                      ·
                        rfl

theorem cell23_7006036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_7006036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006036 prefixEnd_7006036 := by exact prefixLift 7006036
  have htrace : WordTrace (prefixWord ++ tailWord_7006036) baseStart_7006036 baseEnd_7006036 := by
    simpa [prefixWord, tailWord_7006036, baseEnd_7006036] using wordTrace_append hprefix tailTrace_7006036
  have hstable : (prefixWord ++ tailWord_7006036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006036).length < 2 ^ (prefixWord ++ tailWord_7006036).sum := by decide
  have hdescent : baseEnd_7006036 < baseStart_7006036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006042 : List Nat := [3, 1, 1, 2, 1, 3, 3, 9]
def baseStart_7006042 : Nat := 118140960795 + 7006042 * 2 ^ 59
def prefixEnd_7006042 : Nat := 4983230072969 + 3 ^ 40 * 7006042 * 2
def baseEnd_7006042 : Nat := 133239519688414187487215

theorem tailTrace_7006042 : CollatzResearch.WordTrace tailWord_7006042 prefixEnd_7006042 133239519688414187487215 := by
  unfold tailWord_7006042
  simp only [CollatzResearch.WordTrace]
  refine ⟨63882836121078461389389095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170354229656209230371704253 63882836121078461389389095)
  ·
    refine ⟨95824254181617692084083643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63882836121078461389389095 95824254181617692084083643)
    ·
      refine ⟨143736381272426538126125465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95824254181617692084083643 143736381272426538126125465)
      ·
        refine ⟨107802285954319903594594099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143736381272426538126125465 107802285954319903594594099)
        ·
          refine ⟨161703428931479855391891149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107802285954319903594594099 161703428931479855391891149)
          ·
            refine ⟨60638785849304945771959181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161703428931479855391891149 60638785849304945771959181)
            ·
              refine ⟨22739544693489354664484693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60638785849304945771959181 22739544693489354664484693)
              ·
                refine ⟨133239519688414187487215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22739544693489354664484693 133239519688414187487215)
                ·
                  rfl

theorem cell23_7006042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 9].length) (baseStart_7006042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006042 prefixEnd_7006042 := by exact prefixLift 7006042
  have htrace : WordTrace (prefixWord ++ tailWord_7006042) baseStart_7006042 baseEnd_7006042 := by
    simpa [prefixWord, tailWord_7006042, baseEnd_7006042] using wordTrace_append hprefix tailTrace_7006042
  have hstable : (prefixWord ++ tailWord_7006042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006042).length < 2 ^ (prefixWord ++ tailWord_7006042).sum := by decide
  have hdescent : baseEnd_7006042 < baseStart_7006042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006056 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_7006056 : Nat := 118140960795 + 7006056 * 2 ^ 59
def prefixEnd_7006056 : Nat := 4983230072969 + 3 ^ 40 * 7006056 * 2
def baseEnd_7006056 : Nat := 3597474220316346007379741

theorem tailTrace_7006056 : CollatzResearch.WordTrace tailWord_7006056 prefixEnd_7006056 3597474220316346007379741 := by
  unfold tailWord_7006056
  simp only [CollatzResearch.WordTrace]
  refine ⟨127765927553131562974283011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170354570070842083965710681 127765927553131562974283011)
  ·
    refine ⟨191648891329697344461424517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127765927553131562974283011 191648891329697344461424517)
    ·
      refine ⟨35934167124318252086517097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191648891329697344461424517 35934167124318252086517097)
      ·
        refine ⟨26950625343238689064887823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35934167124318252086517097 26950625343238689064887823)
        ·
          refine ⟨40425938014858033597331735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26950625343238689064887823 40425938014858033597331735)
          ·
            refine ⟨60638907022287050395997603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40425938014858033597331735 60638907022287050395997603)
            ·
              refine ⟨90958360533430575593996405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60638907022287050395997603 90958360533430575593996405)
              ·
                refine ⟨8527346300009116461937163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90958360533430575593996405 8527346300009116461937163)
                ·
                  refine ⟨12791019450013674692905745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8527346300009116461937163 12791019450013674692905745)
                  ·
                    refine ⟨9593264587510256019679309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12791019450013674692905745 9593264587510256019679309)
                    ·
                      refine ⟨3597474220316346007379741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9593264587510256019679309 3597474220316346007379741)
                      ·
                        rfl

theorem cell23_7006056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_7006056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006056 prefixEnd_7006056 := by exact prefixLift 7006056
  have htrace : WordTrace (prefixWord ++ tailWord_7006056) baseStart_7006056 baseEnd_7006056 := by
    simpa [prefixWord, tailWord_7006056, baseEnd_7006056] using wordTrace_append hprefix tailTrace_7006056
  have hstable : (prefixWord ++ tailWord_7006056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006056).length < 2 ^ (prefixWord ++ tailWord_7006056).sum := by decide
  have hdescent : baseEnd_7006056 < baseStart_7006056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006079 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 2, 7, 2]
def baseStart_7006079 : Nat := 118140960795 + 7006079 * 2 ^ 59
def prefixEnd_7006079 : Nat := 4983230072969 + 3 ^ 40 * 7006079 * 2
def baseEnd_7006079 : Nat := 3597486030371399417392135

theorem tailTrace_7006079 : CollatzResearch.WordTrace tailWord_7006079 prefixEnd_7006079 3597486030371399417392135 := by
  unfold tailWord_7006079
  simp only [CollatzResearch.WordTrace]
  refine ⟨255532693985179800876653291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170355129323453200584435527 255532693985179800876653291)
  ·
    refine ⟨383299040977769701314979937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255532693985179800876653291 383299040977769701314979937)
    ·
      refine ⟨287474280733327275986234953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383299040977769701314979937 287474280733327275986234953)
      ·
        refine ⟨215605710549995456989676215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287474280733327275986234953 215605710549995456989676215)
        ·
          refine ⟨323408565824993185484514323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215605710549995456989676215 323408565824993185484514323)
          ·
            refine ⟨485112848737489778226771485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323408565824993185484514323 485112848737489778226771485)
            ·
              refine ⟨181917318276558666835039307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485112848737489778226771485 181917318276558666835039307)
              ·
                refine ⟨272875977414838000252558961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181917318276558666835039307 272875977414838000252558961)
                ·
                  refine ⟨204656983061128500189419221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272875977414838000252558961 204656983061128500189419221)
                  ·
                    refine ⟨4796648040495199223189513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 204656983061128500189419221 4796648040495199223189513)
                    ·
                      refine ⟨3597486030371399417392135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796648040495199223189513 3597486030371399417392135)
                      ·
                        rfl

theorem cell23_7006079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_7006079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006079 prefixEnd_7006079 := by exact prefixLift 7006079
  have htrace : WordTrace (prefixWord ++ tailWord_7006079) baseStart_7006079 baseEnd_7006079 := by
    simpa [prefixWord, tailWord_7006079, baseEnd_7006079] using wordTrace_append hprefix tailTrace_7006079
  have hstable : (prefixWord ++ tailWord_7006079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006079).length < 2 ^ (prefixWord ++ tailWord_7006079).sum := by decide
  have hdescent : baseEnd_7006079 < baseStart_7006079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006090 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_7006090 : Nat := 118140960795 + 7006090 * 2 ^ 59
def prefixEnd_7006090 : Nat := 4983230072969 + 3 ^ 40 * 7006090 * 2
def baseEnd_7006090 : Nat := 3597491678658598874354585

theorem tailTrace_7006090 : CollatzResearch.WordTrace tailWord_7006090 prefixEnd_7006090 3597491678658598874354585 := by
  unfold tailWord_7006090
  simp only [CollatzResearch.WordTrace]
  refine ⟨63883273797034987438825931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170355396792093299836869149 63883273797034987438825931)
  ·
    refine ⟨95824910695552481158238897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63883273797034987438825931 95824910695552481158238897)
    ·
      refine ⟨71868683021664360868679173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95824910695552481158238897 71868683021664360868679173)
      ·
        refine ⟨13475378066562067662877345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71868683021664360868679173 13475378066562067662877345)
        ·
          refine ⟨10106533549921550747158009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13475378066562067662877345 10106533549921550747158009)
          ·
            refine ⟨7579900162441163060368507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10106533549921550747158009 7579900162441163060368507)
            ·
              refine ⟨11369850243661744590552761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7579900162441163060368507 11369850243661744590552761)
              ·
                refine ⟨8527387682746308442914571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11369850243661744590552761 8527387682746308442914571)
                ·
                  refine ⟨12791081524119462664371857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8527387682746308442914571 12791081524119462664371857)
                  ·
                    refine ⟨9593311143089596998278893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12791081524119462664371857 9593311143089596998278893)
                    ·
                      refine ⟨3597491678658598874354585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9593311143089596998278893 3597491678658598874354585)
                      ·
                        rfl

theorem cell23_7006090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_7006090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006090 prefixEnd_7006090 := by exact prefixLift 7006090
  have htrace : WordTrace (prefixWord ++ tailWord_7006090) baseStart_7006090 baseEnd_7006090 := by
    simpa [prefixWord, tailWord_7006090, baseEnd_7006090] using wordTrace_append hprefix tailTrace_7006090
  have hstable : (prefixWord ++ tailWord_7006090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006090).length < 2 ^ (prefixWord ++ tailWord_7006090).sum := by decide
  have hdescent : baseEnd_7006090 < baseStart_7006090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006092 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_7006092 : Nat := 118140960795 + 7006092 * 2 ^ 59
def prefixEnd_7006092 : Nat := 4983230072969 + 3 ^ 40 * 7006092 * 2
def baseEnd_7006092 : Nat := 3597492705619907866529575

theorem tailTrace_7006092 : CollatzResearch.WordTrace tailWord_7006092 prefixEnd_7006092 3597492705619907866529575 := by
  unfold tailWord_7006092
  simp only [CollatzResearch.WordTrace]
  refine ⟨127766584067066352048438265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170355445422755136064584353 127766584067066352048438265)
  ·
    refine ⟨95824938050299764036328699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127766584067066352048438265 95824938050299764036328699)
    ·
      refine ⟨143737407075449646054493049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95824938050299764036328699 143737407075449646054493049)
      ·
        refine ⟨107803055306587234540869787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143737407075449646054493049 107803055306587234540869787)
        ·
          refine ⟨161704582959880851811304681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107803055306587234540869787 161704582959880851811304681)
          ·
            refine ⟨121278437219910638858478511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161704582959880851811304681 121278437219910638858478511)
            ·
              refine ⟨181917655829865958287717767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121278437219910638858478511 181917655829865958287717767)
              ·
                refine ⟨272876483744798937431576651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181917655829865958287717767 272876483744798937431576651)
                ·
                  refine ⟨409314725617198406147364977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272876483744798937431576651 409314725617198406147364977)
                  ·
                    refine ⟨306986044212898804610523733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 409314725617198406147364977 306986044212898804610523733)
                    ·
                      refine ⟨3597492705619907866529575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 306986044212898804610523733 3597492705619907866529575)
                      ·
                        rfl

theorem cell23_7006092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_7006092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006092 prefixEnd_7006092 := by exact prefixLift 7006092
  have htrace : WordTrace (prefixWord ++ tailWord_7006092) baseStart_7006092 baseEnd_7006092 := by
    simpa [prefixWord, tailWord_7006092, baseEnd_7006092] using wordTrace_append hprefix tailTrace_7006092
  have hstable : (prefixWord ++ tailWord_7006092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006092).length < 2 ^ (prefixWord ++ tailWord_7006092).sum := by decide
  have hdescent : baseEnd_7006092 < baseStart_7006092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006143 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 2, 2, 2]
def baseStart_7006143 : Nat := 118140960795 + 7006143 * 2 ^ 59
def prefixEnd_7006143 : Nat := 4983230072969 + 3 ^ 40 * 7006143 * 2
def baseEnd_7006143 : Nat := 3597518893133287166991841

theorem tailTrace_7006143 : CollatzResearch.WordTrace tailWord_7006143 prefixEnd_7006143 3597518893133287166991841 := by
  unfold tailWord_7006143
  simp only [CollatzResearch.WordTrace]
  refine ⟨255535028256947939806983083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170356685504631959871322055 255535028256947939806983083)
  ·
    refine ⟨383302542385421909710474625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255535028256947939806983083 383302542385421909710474625)
    ·
      refine ⟨287476906789066432282855969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383302542385421909710474625 287476906789066432282855969)
      ·
        refine ⟨215607680091799824212141977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287476906789066432282855969 215607680091799824212141977)
        ·
          refine ⟨161705760068849868159106483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215607680091799824212141977 161705760068849868159106483)
          ·
            refine ⟨242558640103274802238659725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161705760068849868159106483 242558640103274802238659725)
            ·
              refine ⟨90959490038728050839497397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242558640103274802238659725 90959490038728050839497397)
              ·
                refine ⟨8527452191130754766202881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90959490038728050839497397 8527452191130754766202881)
                ·
                  refine ⟨6395589143348066074652161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8527452191130754766202881 6395589143348066074652161)
                  ·
                    refine ⟨4796691857511049555989121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6395589143348066074652161 4796691857511049555989121)
                    ·
                      refine ⟨3597518893133287166991841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796691857511049555989121 3597518893133287166991841)
                      ·
                        rfl

theorem cell23_7006143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_7006143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006143 prefixEnd_7006143 := by exact prefixLift 7006143
  have htrace : WordTrace (prefixWord ++ tailWord_7006143) baseStart_7006143 baseEnd_7006143 := by
    simpa [prefixWord, tailWord_7006143, baseEnd_7006143] using wordTrace_append hprefix tailTrace_7006143
  have hstable : (prefixWord ++ tailWord_7006143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006143).length < 2 ^ (prefixWord ++ tailWord_7006143).sum := by decide
  have hdescent : baseEnd_7006143 < baseStart_7006143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006159 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 3]
def baseStart_7006159 : Nat := 118140960795 + 7006159 * 2 ^ 59
def prefixEnd_7006159 : Nat := 4983230072969 + 3 ^ 40 * 7006159 * 2
def baseEnd_7006159 : Nat := 3597527108823759104391767

theorem tailTrace_7006159 : CollatzResearch.WordTrace tailWord_7006159 prefixEnd_7006159 3597527108823759104391767 := by
  unfold tailWord_7006159
  simp only [CollatzResearch.WordTrace]
  refine ⟨255535611824889974539565531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170357074549926649693043687 255535611824889974539565531)
  ·
    refine ⟨383303417737334961809348297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255535611824889974539565531 383303417737334961809348297)
    ·
      refine ⟨287477563303001221357011223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383303417737334961809348297 287477563303001221357011223)
      ·
        refine ⟨431216344954501832035516835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287477563303001221357011223 431216344954501832035516835)
        ·
          refine ⟨646824517431752748053275253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431216344954501832035516835 646824517431752748053275253)
          ·
            refine ⟨60639798509226820129994555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 646824517431752748053275253 60639798509226820129994555)
            ·
              refine ⟨90959697763840230194991833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60639798509226820129994555 90959697763840230194991833)
              ·
                refine ⟨68219773322880172646243875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90959697763840230194991833 68219773322880172646243875)
                ·
                  refine ⟨102329659984320258969365813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68219773322880172646243875 102329659984320258969365813)
                  ·
                    refine ⟨9593405623530024278378045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102329659984320258969365813 9593405623530024278378045)
                    ·
                      refine ⟨3597527108823759104391767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9593405623530024278378045 3597527108823759104391767)
                      ·
                        rfl

theorem cell23_7006159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_7006159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006159 prefixEnd_7006159 := by exact prefixLift 7006159
  have htrace : WordTrace (prefixWord ++ tailWord_7006159) baseStart_7006159 baseEnd_7006159 := by
    simpa [prefixWord, tailWord_7006159, baseEnd_7006159] using wordTrace_append hprefix tailTrace_7006159
  have hstable : (prefixWord ++ tailWord_7006159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006159).length < 2 ^ (prefixWord ++ tailWord_7006159).sum := by decide
  have hdescent : baseEnd_7006159 < baseStart_7006159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006209 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 2, 8]
def baseStart_7006209 : Nat := 118140960795 + 7006209 * 2 ^ 59
def prefixEnd_7006209 : Nat := 4983230072969 + 3 ^ 40 * 7006209 * 2
def baseEnd_7006209 : Nat := 1199184260952161302922179

theorem tailTrace_7006209 : CollatzResearch.WordTrace tailWord_7006209 prefixEnd_7006209 1199184260952161302922179 := by
  unfold tailWord_7006209
  simp only [CollatzResearch.WordTrace]
  refine ⟨255537435474708833078885681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170358290316472555385923787 255537435474708833078885681)
  ·
    refine ⟨191653076606031624809164261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255537435474708833078885681 191653076606031624809164261)
    ·
      refine ⟨35934951863630929651718299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191653076606031624809164261 35934951863630929651718299)
      ·
        refine ⟨53902427795446394477577449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35934951863630929651718299 53902427795446394477577449)
        ·
          refine ⟨40426820846584795858183087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53902427795446394477577449 40426820846584795858183087)
          ·
            refine ⟨60640231269877193787274631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40426820846584795858183087 60640231269877193787274631)
            ·
              refine ⟨90960346904815790680911947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60640231269877193787274631 90960346904815790680911947)
              ·
                refine ⟨136440520357223686021367921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90960346904815790680911947 136440520357223686021367921)
                ·
                  refine ⟨102330390267917764516025941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136440520357223686021367921 102330390267917764516025941)
                  ·
                    refine ⟨1199184260952161302922179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102330390267917764516025941 1199184260952161302922179)
                    ·
                      rfl

theorem cell23_7006209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_7006209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006209 prefixEnd_7006209 := by exact prefixLift 7006209
  have htrace : WordTrace (prefixWord ++ tailWord_7006209) baseStart_7006209 baseEnd_7006209 := by
    simpa [prefixWord, tailWord_7006209, baseEnd_7006209] using wordTrace_append hprefix tailTrace_7006209
  have hstable : (prefixWord ++ tailWord_7006209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006209).length < 2 ^ (prefixWord ++ tailWord_7006209).sum := by decide
  have hdescent : baseEnd_7006209 < baseStart_7006209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006216 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_7006216 : Nat := 118140960795 + 7006216 * 2 ^ 59
def prefixEnd_7006216 : Nat := 4983230072969 + 3 ^ 40 * 7006216 * 2
def baseEnd_7006216 : Nat := 3597556377221065381379005

theorem tailTrace_7006216 : CollatzResearch.WordTrace tailWord_7006216 prefixEnd_7006216 3597556377221065381379005 := by
  unfold tailWord_7006216
  simp only [CollatzResearch.WordTrace]
  refine ⟨127768845392841736637195251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170358460523788982182927001 127768845392841736637195251)
  ·
    refine ⟨191653268089262604955792877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127768845392841736637195251 191653268089262604955792877)
    ·
      refine ⟨71869975533473476858422329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191653268089262604955792877 71869975533473476858422329)
      ·
        refine ⟨53902481650105107643816747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71869975533473476858422329 53902481650105107643816747)
        ·
          refine ⟨80853722475157661465725121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53902481650105107643816747 80853722475157661465725121)
          ·
            refine ⟨60640291856368246099293841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80853722475157661465725121 60640291856368246099293841)
            ·
              refine ⟨45480218892276184574470381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60640291856368246099293841 45480218892276184574470381)
              ·
                refine ⟨17055082084603569215426393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45480218892276184574470381 17055082084603569215426393)
                ·
                  refine ⟨12791311563452676911569795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17055082084603569215426393 12791311563452676911569795)
                  ·
                    refine ⟨19186967345179015367354693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12791311563452676911569795 19186967345179015367354693)
                    ·
                      refine ⟨3597556377221065381379005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19186967345179015367354693 3597556377221065381379005)
                      ·
                        rfl

theorem cell23_7006216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_7006216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006216 prefixEnd_7006216 := by exact prefixLift 7006216
  have htrace : WordTrace (prefixWord ++ tailWord_7006216) baseStart_7006216 baseEnd_7006216 := by
    simpa [prefixWord, tailWord_7006216, baseEnd_7006216] using wordTrace_append hprefix tailTrace_7006216
  have hstable : (prefixWord ++ tailWord_7006216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006216).length < 2 ^ (prefixWord ++ tailWord_7006216).sum := by decide
  have hdescent : baseEnd_7006216 < baseStart_7006216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006239 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 8]
def baseStart_7006239 : Nat := 118140960795 + 7006239 * 2 ^ 59
def prefixEnd_7006239 : Nat := 4983230072969 + 3 ^ 40 * 7006239 * 2
def baseEnd_7006239 : Nat := 399729798586235421265711

theorem tailTrace_7006239 : CollatzResearch.WordTrace tailWord_7006239 prefixEnd_7006239 399729798586235421265711 := by
  unfold tailWord_7006239
  simp only [CollatzResearch.WordTrace]
  refine ⟨255538529664600148202477771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170359019776400098801651847 255538529664600148202477771)
  ·
    refine ⟨383307794496900222303716657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255538529664600148202477771 383307794496900222303716657)
    ·
      refine ⟨287480845872675166727787493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383307794496900222303716657 287480845872675166727787493)
      ·
        refine ⟨53902658601126593761460155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287480845872675166727787493 53902658601126593761460155)
        ·
          refine ⟨80853987901689890642190233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53902658601126593761460155 80853987901689890642190233)
          ·
            refine ⟨60640490926267417981642675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80853987901689890642190233 60640490926267417981642675)
            ·
              refine ⟨90960736389401126972464013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60640490926267417981642675 90960736389401126972464013)
              ·
                refine ⟨34110276146025422614674005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90960736389401126972464013 34110276146025422614674005)
                ·
                  refine ⟨399729798586235421265711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34110276146025422614674005 399729798586235421265711)
                  ·
                    rfl

theorem cell23_7006239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 8].length) (baseStart_7006239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006239 prefixEnd_7006239 := by exact prefixLift 7006239
  have htrace : WordTrace (prefixWord ++ tailWord_7006239) baseStart_7006239 baseEnd_7006239 := by
    simpa [prefixWord, tailWord_7006239, baseEnd_7006239] using wordTrace_append hprefix tailTrace_7006239
  have hstable : (prefixWord ++ tailWord_7006239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006239).length < 2 ^ (prefixWord ++ tailWord_7006239).sum := by decide
  have hdescent : baseEnd_7006239 < baseStart_7006239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006256 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 6]
def baseStart_7006256 : Nat := 118140960795 + 7006256 * 2 ^ 59
def prefixEnd_7006256 : Nat := 4983230072969 + 3 ^ 40 * 7006256 * 2
def baseEnd_7006256 : Nat := 399730768494138358319869

theorem tailTrace_7006256 : CollatzResearch.WordTrace tailWord_7006256 prefixEnd_7006256 399730768494138358319869 := by
  unfold tailWord_7006256
  simp only [CollatzResearch.WordTrace]
  refine ⟨127769574852769280052923311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170359433137025706737231081 127769574852769280052923311)
  ·
    refine ⟨191654362279153920079384967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127769574852769280052923311 191654362279153920079384967)
    ·
      refine ⟨287481543418730880119077451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191654362279153920079384967 287481543418730880119077451)
      ·
        refine ⟨431222315128096320178616177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287481543418730880119077451 431222315128096320178616177)
        ·
          refine ⟨323416736346072240133962133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431222315128096320178616177 323416736346072240133962133)
          ·
            refine ⟨15160159516222136256279475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 323416736346072240133962133 15160159516222136256279475)
            ·
              refine ⟨22740239274333204384419213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15160159516222136256279475 22740239274333204384419213)
              ·
                refine ⟨8527589727874951644157205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22740239274333204384419213 8527589727874951644157205)
                ·
                  refine ⟨399730768494138358319869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8527589727874951644157205 399730768494138358319869)
                  ·
                    rfl

theorem cell23_7006256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 6].length) (baseStart_7006256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006256 prefixEnd_7006256 := by exact prefixLift 7006256
  have htrace : WordTrace (prefixWord ++ tailWord_7006256) baseStart_7006256 baseEnd_7006256 := by
    simpa [prefixWord, tailWord_7006256, baseEnd_7006256] using wordTrace_append hprefix tailTrace_7006256
  have hstable : (prefixWord ++ tailWord_7006256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006256).length < 2 ^ (prefixWord ++ tailWord_7006256).sum := by decide
  have hdescent : baseEnd_7006256 < baseStart_7006256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006259 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 6]
def baseStart_7006259 : Nat := 118140960795 + 7006259 * 2 ^ 59
def prefixEnd_7006259 : Nat := 4983230072969 + 3 ^ 40 * 7006259 * 2
def baseEnd_7006259 : Nat := 3597578456889208713141307

theorem tailTrace_7006259 : CollatzResearch.WordTrace tailWord_7006259 prefixEnd_7006259 3597578456889208713141307 := by
  unfold tailWord_7006259
  simp only [CollatzResearch.WordTrace]
  refine ⟨255539259124527691618205831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170359506083018461078803887 255539259124527691618205831)
  ·
    refine ⟨383308888686791537427308747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255539259124527691618205831 383308888686791537427308747)
    ·
      refine ⟨574963333030187306140963121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383308888686791537427308747 574963333030187306140963121)
      ·
        refine ⟨431222499772640479605722341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574963333030187306140963121 431222499772640479605722341)
        ·
          refine ⟨80854218707370089926072939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431222499772640479605722341 80854218707370089926072939)
          ·
            refine ⟨121281328061055134889109409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80854218707370089926072939 121281328061055134889109409)
            ·
              refine ⟨90960996045791351166832057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121281328061055134889109409 90960996045791351166832057)
              ·
                refine ⟨68220747034343513375124043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90960996045791351166832057 68220747034343513375124043)
                ·
                  refine ⟨102331120551515270062686065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68220747034343513375124043 102331120551515270062686065)
                  ·
                    refine ⟨76748340413636452547014549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102331120551515270062686065 76748340413636452547014549)
                    ·
                      refine ⟨3597578456889208713141307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76748340413636452547014549 3597578456889208713141307)
                      ·
                        rfl

theorem cell23_7006259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_7006259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006259 prefixEnd_7006259 := by exact prefixLift 7006259
  have htrace : WordTrace (prefixWord ++ tailWord_7006259) baseStart_7006259 baseEnd_7006259 := by
    simpa [prefixWord, tailWord_7006259, baseEnd_7006259] using wordTrace_append hprefix tailTrace_7006259
  have hstable : (prefixWord ++ tailWord_7006259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006259).length < 2 ^ (prefixWord ++ tailWord_7006259).sum := by decide
  have hdescent : baseEnd_7006259 < baseStart_7006259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006294 : List Nat := [5, 2, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_7006294 : Nat := 118140960795 + 7006294 * 2 ^ 59
def prefixEnd_7006294 : Nat := 4983230072969 + 3 ^ 40 * 7006294 * 2
def baseEnd_7006294 : Nat := 1199198809570705358734549

theorem tailTrace_7006294 : CollatzResearch.WordTrace tailWord_7006294 prefixEnd_7006294 1199198809570705358734549 := by
  unfold tailWord_7006294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15971283479962555787233121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170360357119600595063819957 15971283479962555787233121)
  ·
    refine ⟨11978462609971916840424841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15971283479962555787233121 11978462609971916840424841)
    ·
      refine ⟨8983846957478937630318631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11978462609971916840424841 8983846957478937630318631)
      ·
        refine ⟨13475770436218406445477947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8983846957478937630318631 13475770436218406445477947)
        ·
          refine ⟨20213655654327609668216921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13475770436218406445477947 20213655654327609668216921)
          ·
            refine ⟨15160241740745707251162691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20213655654327609668216921 15160241740745707251162691)
            ·
              refine ⟨22740362611118560876744037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15160241740745707251162691 22740362611118560876744037)
              ·
                refine ⟨4263817989584730164389507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22740362611118560876744037 4263817989584730164389507)
                ·
                  refine ⟨6395726984377095246584261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263817989584730164389507 6395726984377095246584261)
                  ·
                    refine ⟨1199198809570705358734549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6395726984377095246584261 1199198809570705358734549)
                    ·
                      rfl

theorem cell23_7006294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_7006294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006294 prefixEnd_7006294 := by exact prefixLift 7006294
  have htrace : WordTrace (prefixWord ++ tailWord_7006294) baseStart_7006294 baseEnd_7006294 := by
    simpa [prefixWord, tailWord_7006294, baseEnd_7006294] using wordTrace_append hprefix tailTrace_7006294
  have hstable : (prefixWord ++ tailWord_7006294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006294).length < 2 ^ (prefixWord ++ tailWord_7006294).sum := by decide
  have hdescent : baseEnd_7006294 < baseStart_7006294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006316 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_7006316 : Nat := 118140960795 + 7006316 * 2 ^ 59
def prefixEnd_7006316 : Nat := 4983230072969 + 3 ^ 40 * 7006316 * 2
def baseEnd_7006316 : Nat := 1199202575095504996709515

theorem tailTrace_7006316 : CollatzResearch.WordTrace tailWord_7006316 prefixEnd_7006316 1199202575095504996709515 := by
  unfold tailWord_7006316
  simp only [CollatzResearch.WordTrace]
  refine ⟨127770669042660595176515401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170360892056880793568687201 127770669042660595176515401)
  ·
    refine ⟨95828001781995446382386551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127770669042660595176515401 95828001781995446382386551)
    ·
      refine ⟨143742002672993169573579827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95828001781995446382386551 143742002672993169573579827)
      ·
        refine ⟨215613004009489754360369741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143742002672993169573579827 215613004009489754360369741)
        ·
          refine ⟨80854876503558657885138653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215613004009489754360369741 80854876503558657885138653)
          ·
            refine ⟨30320578688834496706926995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80854876503558657885138653 30320578688834496706926995)
            ·
              refine ⟨45480868033251745060390493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30320578688834496706926995 45480868033251745060390493)
              ·
                refine ⟨17055325512469404397646435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45480868033251745060390493 17055325512469404397646435)
                ·
                  refine ⟨25582988268704106596469653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17055325512469404397646435 25582988268704106596469653)
                  ·
                    refine ⟨1199202575095504996709515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25582988268704106596469653 1199202575095504996709515)
                    ·
                      rfl

theorem cell23_7006316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_7006316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006316 prefixEnd_7006316 := by exact prefixLift 7006316
  have htrace : WordTrace (prefixWord ++ tailWord_7006316) baseStart_7006316 baseEnd_7006316 := by
    simpa [prefixWord, tailWord_7006316, baseEnd_7006316] using wordTrace_append hprefix tailTrace_7006316
  have hstable : (prefixWord ++ tailWord_7006316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006316).length < 2 ^ (prefixWord ++ tailWord_7006316).sum := by decide
  have hdescent : baseEnd_7006316 < baseStart_7006316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006337 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 1, 5]
def baseStart_7006337 : Nat := 118140960795 + 7006337 * 2 ^ 59
def prefixEnd_7006337 : Nat := 4983230072969 + 3 ^ 40 * 7006337 * 2
def baseEnd_7006337 : Nat := 1199206169460086469321983

theorem tailTrace_7006337 : CollatzResearch.WordTrace tailWord_7006337 prefixEnd_7006337 1199206169460086469321983 := by
  unfold tailWord_7006337
  simp only [CollatzResearch.WordTrace]
  refine ⟨255542104018245110939545265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170361402678830073959696843 255542104018245110939545265)
  ·
    refine ⟨191656578013683833204658949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255542104018245110939545265 191656578013683833204658949)
    ·
      refine ⟨35935608377565718725873553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191656578013683833204658949 35935608377565718725873553)
      ·
        refine ⟨26951706283174289044405165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35935608377565718725873553 26951706283174289044405165)
        ·
          refine ⟨10106889856190358391651937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26951706283174289044405165 10106889856190358391651937)
          ·
            refine ⟨7580167392142768793738953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10106889856190358391651937 7580167392142768793738953)
            ·
              refine ⟨5685125544107076595304215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7580167392142768793738953 5685125544107076595304215)
              ·
                refine ⟨8527688316160614892956323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5685125544107076595304215 8527688316160614892956323)
                ·
                  refine ⟨12791532474240922339434485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8527688316160614892956323 12791532474240922339434485)
                  ·
                    refine ⟨1199206169460086469321983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12791532474240922339434485 1199206169460086469321983)
                    ·
                      rfl

theorem cell23_7006337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_7006337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006337 prefixEnd_7006337 := by exact prefixLift 7006337
  have htrace : WordTrace (prefixWord ++ tailWord_7006337) baseStart_7006337 baseEnd_7006337 := by
    simpa [prefixWord, tailWord_7006337, baseEnd_7006337] using wordTrace_append hprefix tailTrace_7006337
  have hstable : (prefixWord ++ tailWord_7006337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006337).length < 2 ^ (prefixWord ++ tailWord_7006337).sum := by decide
  have hdescent : baseEnd_7006337 < baseStart_7006337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006340 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_7006340 : Nat := 118140960795 + 7006340 * 2 ^ 59
def prefixEnd_7006340 : Nat := 4983230072969 + 3 ^ 40 * 7006340 * 2
def baseEnd_7006340 : Nat := 3597620048822222896228435

theorem tailTrace_7006340 : CollatzResearch.WordTrace tailWord_7006340 prefixEnd_7006340 3597620048822222896228435 := by
  unfold tailWord_7006340
  simp only [CollatzResearch.WordTrace]
  refine ⟨127771106718617121225952237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170361475624822828301269649 127771106718617121225952237)
  ·
    refine ⟨47914165019481420459732089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127771106718617121225952237 47914165019481420459732089)
    ·
      refine ⟨35935623764611065344799067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47914165019481420459732089 35935623764611065344799067)
      ·
        refine ⟨53903435646916598017198601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35935623764611065344799067 53903435646916598017198601)
        ·
          refine ⟨40427576735187448512898951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53903435646916598017198601 40427576735187448512898951)
          ·
            refine ⟨60641365102781172769348427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40427576735187448512898951 60641365102781172769348427)
            ·
              refine ⟨90962047654171759154022641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60641365102781172769348427 90962047654171759154022641)
              ·
                refine ⟨68221535740628819365516981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90962047654171759154022641 68221535740628819365516981)
                ·
                  refine ⟨6395768975683951815517217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68221535740628819365516981 6395768975683951815517217)
                  ·
                    refine ⟨4796826731762963861637913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6395768975683951815517217 4796826731762963861637913)
                    ·
                      refine ⟨3597620048822222896228435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796826731762963861637913 3597620048822222896228435)
                      ·
                        rfl

theorem cell23_7006340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_7006340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006340 prefixEnd_7006340 := by exact prefixLift 7006340
  have htrace : WordTrace (prefixWord ++ tailWord_7006340) baseStart_7006340 baseEnd_7006340 := by
    simpa [prefixWord, tailWord_7006340, baseEnd_7006340] using wordTrace_append hprefix tailTrace_7006340
  have hstable : (prefixWord ++ tailWord_7006340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006340).length < 2 ^ (prefixWord ++ tailWord_7006340).sum := by decide
  have hdescent : baseEnd_7006340 < baseStart_7006340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006346 : List Nat := [3, 1, 2, 3, 1, 3, 10]
def baseStart_7006346 : Nat := 118140960795 + 7006346 * 2 ^ 59
def prefixEnd_7006346 : Nat := 4983230072969 + 3 ^ 40 * 7006346 * 2
def baseEnd_7006346 : Nat := 44415100366742591021647

theorem tailTrace_7006346 : CollatzResearch.WordTrace tailWord_7006346 prefixEnd_7006346 44415100366742591021647 := by
  unfold tailWord_7006346
  simp only [CollatzResearch.WordTrace]
  refine ⟨63885608068803126369155723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170361621516808336984415261 63885608068803126369155723)
  ·
    refine ⟨95828412103204689553733585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63885608068803126369155723 95828412103204689553733585)
    ·
      refine ⟨71871309077403517165300189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95828412103204689553733585 71871309077403517165300189)
      ·
        refine ⟨26951740904026318936987571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71871309077403517165300189 26951740904026318936987571)
        ·
          refine ⟨40427611356039478405481357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26951740904026318936987571 40427611356039478405481357)
          ·
            refine ⟨15160354258514804402055509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40427611356039478405481357 15160354258514804402055509)
            ·
              refine ⟨44415100366742591021647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15160354258514804402055509 44415100366742591021647)
              ·
                rfl

theorem cell23_7006346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 10].length) (baseStart_7006346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006346 prefixEnd_7006346 := by exact prefixLift 7006346
  have htrace : WordTrace (prefixWord ++ tailWord_7006346) baseStart_7006346 baseEnd_7006346 := by
    simpa [prefixWord, tailWord_7006346, baseEnd_7006346] using wordTrace_append hprefix tailTrace_7006346
  have hstable : (prefixWord ++ tailWord_7006346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006346).length < 2 ^ (prefixWord ++ tailWord_7006346).sum := by decide
  have hdescent : baseEnd_7006346 < baseStart_7006346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006350 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_7006350 : Nat := 118140960795 + 7006350 * 2 ^ 59
def prefixEnd_7006350 : Nat := 4983230072969 + 3 ^ 40 * 7006350 * 2
def baseEnd_7006350 : Nat := 1199208394542922619034463

theorem tailTrace_7006350 : CollatzResearch.WordTrace tailWord_7006350 prefixEnd_7006350 1199208394542922619034463 := by
  unfold tailWord_7006350
  simp only [CollatzResearch.WordTrace]
  refine ⟨31942822270899751769971063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170361718778132009439845669 31942822270899751769971063)
  ·
    refine ⟨47914233406349627654956595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31942822270899751769971063 47914233406349627654956595)
    ·
      refine ⟨71871350109524441482434893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47914233406349627654956595 71871350109524441482434893)
      ·
        refine ⟨26951756291071665555913085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71871350109524441482434893 26951756291071665555913085)
        ·
          refine ⟨10106908609151874583467407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26951756291071665555913085 10106908609151874583467407)
          ·
            refine ⟨15160362913727811875201111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10106908609151874583467407 15160362913727811875201111)
            ·
              refine ⟨22740544370591717812801667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15160362913727811875201111 22740544370591717812801667)
              ·
                refine ⟨34110816555887576719202501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22740544370591717812801667 34110816555887576719202501)
                ·
                  refine ⟨6395778104228920634850469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34110816555887576719202501 6395778104228920634850469)
                  ·
                    refine ⟨1199208394542922619034463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6395778104228920634850469 1199208394542922619034463)
                    ·
                      rfl

theorem cell23_7006350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_7006350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006350 prefixEnd_7006350 := by exact prefixLift 7006350
  have htrace : WordTrace (prefixWord ++ tailWord_7006350) baseStart_7006350 baseEnd_7006350 := by
    simpa [prefixWord, tailWord_7006350, baseEnd_7006350] using wordTrace_append hprefix tailTrace_7006350
  have hstable : (prefixWord ++ tailWord_7006350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006350).length < 2 ^ (prefixWord ++ tailWord_7006350).sum := by decide
  have hdescent : baseEnd_7006350 < baseStart_7006350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006357 : List Nat := [1, 3, 2, 1, 1, 1, 3, 6, 1, 2, 2]
def baseStart_7006357 : Nat := 118140960795 + 7006357 * 2 ^ 59
def prefixEnd_7006357 : Nat := 4983230072969 + 3 ^ 40 * 7006357 * 2
def baseEnd_7006357 : Nat := 3597628777993349329715857

theorem tailTrace_7006357 : CollatzResearch.WordTrace tailWord_7006357 prefixEnd_7006357 3597628777993349329715857 := by
  unfold tailWord_7006357
  simp only [CollatzResearch.WordTrace]
  refine ⟨255542833478172654355273325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170361888985448436236848883 255542833478172654355273325)
  ·
    refine ⟨95828562554314745383227497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255542833478172654355273325 95828562554314745383227497)
    ·
      refine ⟨71871421915736059037420623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95828562554314745383227497 71871421915736059037420623)
      ·
        refine ⟨107807132873604088556130935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71871421915736059037420623 107807132873604088556130935)
        ·
          refine ⟨161710699310406132834196403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107807132873604088556130935 161710699310406132834196403)
          ·
            refine ⟨242566048965609199251294605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161710699310406132834196403 242566048965609199251294605)
            ·
              refine ⟨90962268362103449719235477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242566048965609199251294605 90962268362103449719235477)
              ·
                refine ⟨4263856329473599205589163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90962268362103449719235477 4263856329473599205589163)
                ·
                  refine ⟨6395784494210398808383745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263856329473599205589163 6395784494210398808383745)
                  ·
                    refine ⟨4796838370657799106287809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6395784494210398808383745 4796838370657799106287809)
                    ·
                      refine ⟨3597628777993349329715857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796838370657799106287809 3597628777993349329715857)
                      ·
                        rfl

theorem cell23_7006357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_7006357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006357 prefixEnd_7006357 := by exact prefixLift 7006357
  have htrace : WordTrace (prefixWord ++ tailWord_7006357) baseStart_7006357 baseEnd_7006357 := by
    simpa [prefixWord, tailWord_7006357, baseEnd_7006357] using wordTrace_append hprefix tailTrace_7006357
  have hstable : (prefixWord ++ tailWord_7006357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006357).length < 2 ^ (prefixWord ++ tailWord_7006357).sum := by decide
  have hdescent : baseEnd_7006357 < baseStart_7006357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006367 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 2, 4]
def baseStart_7006367 : Nat := 118140960795 + 7006367 * 2 ^ 59
def prefixEnd_7006367 : Nat := 4983230072969 + 3 ^ 40 * 7006367 * 2
def baseEnd_7006367 : Nat := 1199211304266631430196937

theorem tailTrace_7006367 : CollatzResearch.WordTrace tailWord_7006367 prefixEnd_7006367 1199211304266631430196937 := by
  unfold tailWord_7006367
  simp only [CollatzResearch.WordTrace]
  refine ⟨255543198208136426063137355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170362132138757617375424903 255543198208136426063137355)
  ·
    refine ⟨383314797312204639094706033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255543198208136426063137355 383314797312204639094706033)
    ·
      refine ⟨287486097984153479321029525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383314797312204639094706033 287486097984153479321029525)
      ·
        refine ⟨13475910843007194343173259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 287486097984153479321029525 13475910843007194343173259)
        ·
          refine ⟨20213866264510791514759889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13475910843007194343173259 20213866264510791514759889)
          ·
            refine ⟨15160399698383093636069917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20213866264510791514759889 15160399698383093636069917)
            ·
              refine ⟨5685149886893660113526219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15160399698383093636069917 5685149886893660113526219)
              ·
                refine ⟨8527724830340490170289329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5685149886893660113526219 8527724830340490170289329)
                ·
                  refine ⟨6395793622755367627716997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8527724830340490170289329 6395793622755367627716997)
                  ·
                    refine ⟨1199211304266631430196937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6395793622755367627716997 1199211304266631430196937)
                    ·
                      rfl

theorem cell23_7006367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 4].length) (baseStart_7006367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006367 prefixEnd_7006367 := by exact prefixLift 7006367
  have htrace : WordTrace (prefixWord ++ tailWord_7006367) baseStart_7006367 baseEnd_7006367 := by
    simpa [prefixWord, tailWord_7006367, baseEnd_7006367] using wordTrace_append hprefix tailTrace_7006367
  have hstable : (prefixWord ++ tailWord_7006367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006367).length < 2 ^ (prefixWord ++ tailWord_7006367).sum := by decide
  have hdescent : baseEnd_7006367 < baseStart_7006367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006370 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_7006370 : Nat := 118140960795 + 7006370 * 2 ^ 59
def prefixEnd_7006370 : Nat := 4983230072969 + 3 ^ 40 * 7006370 * 2
def baseEnd_7006370 : Nat := 3597635453241857778853297

theorem tailTrace_7006370 : CollatzResearch.WordTrace tailWord_7006370 prefixEnd_7006370 3597635453241857778853297 := by
  unfold tailWord_7006370
  simp only [CollatzResearch.WordTrace]
  refine ⟨63885826906781389393874141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170362205084750371716997709 63885826906781389393874141)
  ·
    refine ⟨23957185090043021022702803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63885826906781389393874141 23957185090043021022702803)
    ·
      refine ⟨35935777635064531534054205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23957185090043021022702803 35935777635064531534054205)
      ·
        refine ⟨13475916613149199325270327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35935777635064531534054205 13475916613149199325270327)
        ·
          refine ⟨20213874919723798987905491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13475916613149199325270327 20213874919723798987905491)
          ·
            refine ⟨30320812379585698481858237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20213874919723798987905491 30320812379585698481858237)
            ·
              refine ⟨11370304642344636930696839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30320812379585698481858237 11370304642344636930696839)
              ·
                refine ⟨17055456963516955396045259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11370304642344636930696839 17055456963516955396045259)
                ·
                  refine ⟨25583185445275433094067889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17055456963516955396045259 25583185445275433094067889)
                  ·
                    refine ⟨19187389083956574820550917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25583185445275433094067889 19187389083956574820550917)
                    ·
                      refine ⟨3597635453241857778853297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19187389083956574820550917 3597635453241857778853297)
                      ·
                        rfl

theorem cell23_7006370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_7006370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006370 prefixEnd_7006370 := by exact prefixLift 7006370
  have htrace : WordTrace (prefixWord ++ tailWord_7006370) baseStart_7006370 baseEnd_7006370 := by
    simpa [prefixWord, tailWord_7006370, baseEnd_7006370] using wordTrace_append hprefix tailTrace_7006370
  have hstable : (prefixWord ++ tailWord_7006370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006370).length < 2 ^ (prefixWord ++ tailWord_7006370).sum := by decide
  have hdescent : baseEnd_7006370 < baseStart_7006370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006386 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_7006386 : Nat := 118140960795 + 7006386 * 2 ^ 59
def prefixEnd_7006386 : Nat := 4983230072969 + 3 ^ 40 * 7006386 * 2
def baseEnd_7006386 : Nat := 3597643668932329716253223

theorem tailTrace_7006386 : CollatzResearch.WordTrace tailWord_7006386 prefixEnd_7006386 3597643668932329716253223 := by
  unfold tailWord_7006386
  simp only [CollatzResearch.WordTrace]
  refine ⟨63885972798766898077019753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170362594130045061538719341 63885972798766898077019753)
  ·
    refine ⟨47914479599075173557764815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63885972798766898077019753 47914479599075173557764815)
    ·
      refine ⟨71871719398612760336647223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47914479599075173557764815 71871719398612760336647223)
      ·
        refine ⟨107807579097919140504970835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71871719398612760336647223 107807579097919140504970835)
        ·
          refine ⟨161711368646878710757456253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107807579097919140504970835 161711368646878710757456253)
          ·
            refine ⟨60641763242579516534046095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161711368646878710757456253 60641763242579516534046095)
            ·
              refine ⟨90962644863869274801069143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60641763242579516534046095 90962644863869274801069143)
              ·
                refine ⟨136443967295803912201603715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90962644863869274801069143 136443967295803912201603715)
                ·
                  refine ⟨204665950943705868302405573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136443967295803912201603715 204665950943705868302405573)
                  ·
                    refine ⟨38374865801944850306701045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204665950943705868302405573 38374865801944850306701045)
                    ·
                      refine ⟨3597643668932329716253223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38374865801944850306701045 3597643668932329716253223)
                      ·
                        rfl

theorem cell23_7006386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_7006386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006386 prefixEnd_7006386 := by exact prefixLift 7006386
  have htrace : WordTrace (prefixWord ++ tailWord_7006386) baseStart_7006386 baseEnd_7006386 := by
    simpa [prefixWord, tailWord_7006386, baseEnd_7006386] using wordTrace_append hprefix tailTrace_7006386
  have hstable : (prefixWord ++ tailWord_7006386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006386).length < 2 ^ (prefixWord ++ tailWord_7006386).sum := by decide
  have hdescent : baseEnd_7006386 < baseStart_7006386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006424 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 2, 1, 3]
def baseStart_7006424 : Nat := 118140960795 + 7006424 * 2 ^ 59
def prefixEnd_7006424 : Nat := 4983230072969 + 3 ^ 40 * 7006424 * 2
def baseEnd_7006424 : Nat := 3597663181197200567578049

theorem tailTrace_7006424 : CollatzResearch.WordTrace tailWord_7006424 prefixEnd_7006424 3597663181197200567578049 := by
  unfold tailWord_7006424
  simp only [CollatzResearch.WordTrace]
  refine ⟨127772638584464962398981163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170363518112619949865308217 127772638584464962398981163)
  ·
    refine ⟨191658957876697443598471745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127772638584464962398981163 191658957876697443598471745)
    ·
      refine ⟨143744218407523082698853809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191658957876697443598471745 143744218407523082698853809)
      ·
        refine ⟨107808163805642312024140357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143744218407523082698853809 107808163805642312024140357)
        ·
          refine ⟨20214030713557933504526317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107808163805642312024140357 20214030713557933504526317)
          ·
            refine ⟨7580261517584225064197369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20214030713557933504526317 7580261517584225064197369)
            ·
              refine ⟨5685196138188168798148027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7580261517584225064197369 5685196138188168798148027)
              ·
                refine ⟨8527794207282253197222041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5685196138188168798148027 8527794207282253197222041)
                ·
                  refine ⟨6395845655461689897916531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8527794207282253197222041 6395845655461689897916531)
                  ·
                    refine ⟨9593768483192534846874797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6395845655461689897916531 9593768483192534846874797)
                    ·
                      refine ⟨3597663181197200567578049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9593768483192534846874797 3597663181197200567578049)
                      ·
                        rfl

theorem cell23_7006424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_7006424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006424 prefixEnd_7006424 := by exact prefixLift 7006424
  have htrace : WordTrace (prefixWord ++ tailWord_7006424) baseStart_7006424 baseEnd_7006424 := by
    simpa [prefixWord, tailWord_7006424, baseEnd_7006424] using wordTrace_append hprefix tailTrace_7006424
  have hstable : (prefixWord ++ tailWord_7006424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006424).length < 2 ^ (prefixWord ++ tailWord_7006424).sum := by decide
  have hdescent : baseEnd_7006424 < baseStart_7006424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006436 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 9]
def baseStart_7006436 : Nat := 118140960795 + 7006436 * 2 ^ 59
def prefixEnd_7006436 : Nat := 4983230072969 + 3 ^ 40 * 7006436 * 2
def baseEnd_7006436 : Nat := 399741038107228280069777

theorem tailTrace_7006436 : CollatzResearch.WordTrace tailWord_7006436 prefixEnd_7006436 399741038107228280069777 := by
  unfold tailWord_7006436
  simp only [CollatzResearch.WordTrace]
  refine ⟨127772857422443225423699581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170363809896590967231599441 127772857422443225423699581)
  ·
    refine ⟨47914821533416209533887343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127772857422443225423699581 47914821533416209533887343)
    ·
      refine ⟨71872232300124314300831015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47914821533416209533887343 71872232300124314300831015)
      ·
        refine ⟨107808348450186471451246523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71872232300124314300831015 107808348450186471451246523)
        ·
          refine ⟨161712522675279707176869785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107808348450186471451246523 161712522675279707176869785)
          ·
            refine ⟨121284392006459780382652339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161712522675279707176869785 121284392006459780382652339)
            ·
              refine ⟨181926588009689670573978509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121284392006459780382652339 181926588009689670573978509)
              ·
                refine ⟨68222470503633626465241941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181926588009689670573978509 68222470503633626465241941)
                ·
                  refine ⟨399741038107228280069777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68222470503633626465241941 399741038107228280069777)
                  ·
                    rfl

theorem cell23_7006436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_7006436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006436 prefixEnd_7006436 := by exact prefixLift 7006436
  have htrace : WordTrace (prefixWord ++ tailWord_7006436) baseStart_7006436 baseEnd_7006436 := by
    simpa [prefixWord, tailWord_7006436, baseEnd_7006436] using wordTrace_append hprefix tailTrace_7006436
  have hstable : (prefixWord ++ tailWord_7006436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006436).length < 2 ^ (prefixWord ++ tailWord_7006436).sum := by decide
  have hdescent : baseEnd_7006436 < baseStart_7006436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006463 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 3]
def baseStart_7006463 : Nat := 118140960795 + 7006463 * 2 ^ 59
def prefixEnd_7006463 : Nat := 4983230072969 + 3 ^ 40 * 7006463 * 2
def baseEnd_7006463 : Nat := 3597683206942725914990369

theorem tailTrace_7006463 : CollatzResearch.WordTrace tailWord_7006463 prefixEnd_7006463 3597683206942725914990369 := by
  unfold tailWord_7006463
  simp only [CollatzResearch.WordTrace]
  refine ⟨255546699615788634458632043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170364466410525756305754695 255546699615788634458632043)
  ·
    refine ⟨383320049423682951687948065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255546699615788634458632043 383320049423682951687948065)
    ·
      refine ⟨287490037067762213765961049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383320049423682951687948065 287490037067762213765961049)
      ·
        refine ⟨215617527800821660324470787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287490037067762213765961049 215617527800821660324470787)
        ·
          refine ⟨323426291701232490486706181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215617527800821660324470787 323426291701232490486706181)
          ·
            refine ⟨60642429693981091966257409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323426291701232490486706181 60642429693981091966257409)
            ·
              refine ⟨45481822270485818974693057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60642429693981091966257409 45481822270485818974693057)
              ·
                refine ⟨34111366702864364231019793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45481822270485818974693057 34111366702864364231019793)
                ·
                  refine ⟨25583525027148273173264845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34111366702864364231019793 25583525027148273173264845)
                  ·
                    refine ⟨9593821885180602439974317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25583525027148273173264845 9593821885180602439974317)
                    ·
                      refine ⟨3597683206942725914990369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9593821885180602439974317 3597683206942725914990369)
                      ·
                        rfl

theorem cell23_7006463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_7006463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006463 prefixEnd_7006463 := by exact prefixLift 7006463
  have htrace : WordTrace (prefixWord ++ tailWord_7006463) baseStart_7006463 baseEnd_7006463 := by
    simpa [prefixWord, tailWord_7006463, baseEnd_7006463] using wordTrace_append hprefix tailTrace_7006463
  have hstable : (prefixWord ++ tailWord_7006463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006463).length < 2 ^ (prefixWord ++ tailWord_7006463).sum := by decide
  have hdescent : baseEnd_7006463 < baseStart_7006463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006500 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_7006500 : Nat := 118140960795 + 7006500 * 2 ^ 59
def prefixEnd_7006500 : Nat := 4983230072969 + 3 ^ 40 * 7006500 * 2
def baseEnd_7006500 : Nat := 1199234068575647423409233

theorem tailTrace_7006500 : CollatzResearch.WordTrace tailWord_7006500 prefixEnd_7006500 1199234068575647423409233 := by
  unfold tailWord_7006500
  simp only [CollatzResearch.WordTrace]
  refine ⟨127774024558327294888864477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170365366077769726518485969 127774024558327294888864477)
  ·
    refine ⟨47915259209372735583324179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127774024558327294888864477 47915259209372735583324179)
    ·
      refine ⟨71872888814059103374986269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47915259209372735583324179 71872888814059103374986269)
      ·
        refine ⟨26952333305272163765619851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71872888814059103374986269 26952333305272163765619851)
        ·
          refine ⟨40428499957908245648429777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26952333305272163765619851 40428499957908245648429777)
          ·
            refine ⟨30321374968431184236322333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40428499957908245648429777 30321374968431184236322333)
            ·
              refine ⟨11370515613161694088620875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30321374968431184236322333 11370515613161694088620875)
              ·
                refine ⟨17055773419742541132931313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11370515613161694088620875 17055773419742541132931313)
                ·
                  refine ⟨12791830064806905849698485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17055773419742541132931313 12791830064806905849698485)
                  ·
                    refine ⟨1199234068575647423409233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12791830064806905849698485 1199234068575647423409233)
                    ·
                      rfl

theorem cell23_7006500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_7006500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006500 prefixEnd_7006500 := by exact prefixLift 7006500
  have htrace : WordTrace (prefixWord ++ tailWord_7006500) baseStart_7006500 baseEnd_7006500 := by
    simpa [prefixWord, tailWord_7006500, baseEnd_7006500] using wordTrace_append hprefix tailTrace_7006500
  have hstable : (prefixWord ++ tailWord_7006500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006500).length < 2 ^ (prefixWord ++ tailWord_7006500).sum := by decide
  have hdescent : baseEnd_7006500 < baseStart_7006500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006520 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 2, 4, 2]
def baseStart_7006520 : Nat := 118140960795 + 7006520 * 2 ^ 59
def prefixEnd_7006520 : Nat := 4983230072969 + 3 ^ 40 * 7006520 * 2
def baseEnd_7006520 : Nat := 3597712475340032191977607

theorem tailTrace_7006520 : CollatzResearch.WordTrace tailWord_7006520 prefixEnd_7006520 3597712475340032191977607 := by
  unfold tailWord_7006520
  simp only [CollatzResearch.WordTrace]
  refine ⟨127774389288291066596728507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170365852384388088795638009 127774389288291066596728507)
  ·
    refine ⟨191661583932436599895092761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127774389288291066596728507 191661583932436599895092761)
    ·
      refine ⟨143746187949327449921319571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191661583932436599895092761 143746187949327449921319571)
      ·
        refine ⟨215619281923991174881979357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143746187949327449921319571 215619281923991174881979357)
        ·
          refine ⟨80857230721496690580742259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215619281923991174881979357 80857230721496690580742259)
          ·
            refine ⟨121285846082245035871113389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80857230721496690580742259 121285846082245035871113389)
            ·
              refine ⟨45482192280841888451667521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121285846082245035871113389 45482192280841888451667521)
              ·
                refine ⟨34111644210631416338750641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45482192280841888451667521 34111644210631416338750641)
                ·
                  refine ⟨25583733157973562254062981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34111644210631416338750641 25583733157973562254062981)
                  ·
                    refine ⟨4796949967120042922636809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25583733157973562254062981 4796949967120042922636809)
                    ·
                      refine ⟨3597712475340032191977607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4796949967120042922636809 3597712475340032191977607)
                      ·
                        rfl

theorem cell23_7006520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_7006520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006520 prefixEnd_7006520 := by exact prefixLift 7006520
  have htrace : WordTrace (prefixWord ++ tailWord_7006520) baseStart_7006520 baseEnd_7006520 := by
    simpa [prefixWord, tailWord_7006520, baseEnd_7006520] using wordTrace_append hprefix tailTrace_7006520
  have hstable : (prefixWord ++ tailWord_7006520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006520).length < 2 ^ (prefixWord ++ tailWord_7006520).sum := by decide
  have hdescent : baseEnd_7006520 < baseStart_7006520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006553 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 3]
def baseStart_7006553 : Nat := 118140960795 + 7006553 * 2 ^ 59
def prefixEnd_7006553 : Nat := 4983230072969 + 3 ^ 40 * 7006553 * 2
def baseEnd_7006553 : Nat := 3597729420201630562864955

theorem tailTrace_7006553 : CollatzResearch.WordTrace tailWord_7006553 prefixEnd_7006553 3597729420201630562864955 := by
  unfold tailWord_7006553
  simp only [CollatzResearch.WordTrace]
  refine ⟨255549982185462579829408313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170366654790308386552938875 255549982185462579829408313)
  ·
    refine ⟨191662486639096934872056235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255549982185462579829408313 191662486639096934872056235)
    ·
      refine ⟨287493729958645402308084353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191662486639096934872056235 287493729958645402308084353)
      ·
        refine ⟨215620297468984051731063265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287493729958645402308084353 215620297468984051731063265)
        ·
          refine ⟨161715223101738038798297449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215620297468984051731063265 161715223101738038798297449)
          ·
            refine ⟨121286417326303529098723087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161715223101738038798297449 121286417326303529098723087)
            ·
              refine ⟨181929625989455293648084631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121286417326303529098723087 181929625989455293648084631)
              ·
                refine ⟨272894438984182940472126947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181929625989455293648084631 272894438984182940472126947)
                ·
                  refine ⟨409341658476274410708190421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272894438984182940472126947 409341658476274410708190421)
                  ·
                    refine ⟨9593945120537681500973213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 409341658476274410708190421 9593945120537681500973213)
                    ·
                      refine ⟨3597729420201630562864955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9593945120537681500973213 3597729420201630562864955)
                      ·
                        rfl

theorem cell23_7006553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_7006553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006553 prefixEnd_7006553 := by exact prefixLift 7006553
  have htrace : WordTrace (prefixWord ++ tailWord_7006553) baseStart_7006553 baseEnd_7006553 := by
    simpa [prefixWord, tailWord_7006553, baseEnd_7006553] using wordTrace_append hprefix tailTrace_7006553
  have hstable : (prefixWord ++ tailWord_7006553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006553).length < 2 ^ (prefixWord ++ tailWord_7006553).sum := by decide
  have hdescent : baseEnd_7006553 < baseStart_7006553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006581 : List Nat := [1, 3, 4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_7006581 : Nat := 118140960795 + 7006581 * 2 ^ 59
def prefixEnd_7006581 : Nat := 4983230072969 + 3 ^ 40 * 7006581 * 2
def baseEnd_7006581 : Nat := 1199247932553318817771609

theorem tailTrace_7006581 : CollatzResearch.WordTrace tailWord_7006581 prefixEnd_7006581 1199247932553318817771609 := by
  unfold tailWord_7006581
  simp only [CollatzResearch.WordTrace]
  refine ⟨255551003429361140611427597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170367335619574093740951731 255551003429361140611427597)
  ·
    refine ⟨95831626286010427729285349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255551003429361140611427597 95831626286010427729285349)
    ·
      refine ⟨17968429928626955199241003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95831626286010427729285349 17968429928626955199241003)
      ·
        refine ⟨26952644892940432798861505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17968429928626955199241003 26952644892940432798861505)
        ·
          refine ⟨20214483669705324599146129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26952644892940432798861505 20214483669705324599146129)
          ·
            refine ⟨15160862752278993449359597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20214483669705324599146129 15160862752278993449359597)
            ·
              refine ⟨5685323532104622543509849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15160862752278993449359597 5685323532104622543509849)
              ·
                refine ⟨4263992649078466907632387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5685323532104622543509849 4263992649078466907632387)
                ·
                  refine ⟨6395988973617700361448581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263992649078466907632387 6395988973617700361448581)
                  ·
                    refine ⟨1199247932553318817771609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6395988973617700361448581 1199247932553318817771609)
                    ·
                      rfl

theorem cell23_7006581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_7006581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006581 prefixEnd_7006581 := by exact prefixLift 7006581
  have htrace : WordTrace (prefixWord ++ tailWord_7006581) baseStart_7006581 baseEnd_7006581 := by
    simpa [prefixWord, tailWord_7006581, baseEnd_7006581] using wordTrace_append hprefix tailTrace_7006581
  have hstable : (prefixWord ++ tailWord_7006581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006581).length < 2 ^ (prefixWord ++ tailWord_7006581).sum := by decide
  have hdescent : baseEnd_7006581 < baseStart_7006581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006587 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 3]
def baseStart_7006587 : Nat := 118140960795 + 7006587 * 2 ^ 59
def prefixEnd_7006587 : Nat := 4983230072969 + 3 ^ 40 * 7006587 * 2
def baseEnd_7006587 : Nat := 3597746878543883429839799

theorem tailTrace_7006587 : CollatzResearch.WordTrace tailWord_7006587 prefixEnd_7006587 3597746878543883429839799 := by
  unfold tailWord_7006587
  simp only [CollatzResearch.WordTrace]
  refine ⟨255551222267339403636146015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170367481511559602424097343 255551222267339403636146015)
  ·
    refine ⟨383326833401009105454219023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255551222267339403636146015 383326833401009105454219023)
    ·
      refine ⟨574990250101513658181328535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383326833401009105454219023 574990250101513658181328535)
      ·
        refine ⟨862485375152270487271992803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574990250101513658181328535 862485375152270487271992803)
        ·
          refine ⟨1293728062728405730907989205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862485375152270487271992803 1293728062728405730907989205)
          ·
            refine ⟨30321751470197009318155997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1293728062728405730907989205 30321751470197009318155997)
            ·
              refine ⟨11370656801323878494308499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30321751470197009318155997 11370656801323878494308499)
              ·
                refine ⟨17055985201985817741462749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11370656801323878494308499 17055985201985817741462749)
                ·
                  refine ⟨6395994450744681653048531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17055985201985817741462749 6395994450744681653048531)
                  ·
                    refine ⟨9593991676117022479572797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6395994450744681653048531 9593991676117022479572797)
                    ·
                      refine ⟨3597746878543883429839799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9593991676117022479572797 3597746878543883429839799)
                      ·
                        rfl

theorem cell23_7006587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 3].length) (baseStart_7006587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006587 prefixEnd_7006587 := by exact prefixLift 7006587
  have htrace : WordTrace (prefixWord ++ tailWord_7006587) baseStart_7006587 baseEnd_7006587 := by
    simpa [prefixWord, tailWord_7006587, baseEnd_7006587] using wordTrace_append hprefix tailTrace_7006587
  have hstable : (prefixWord ++ tailWord_7006587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006587).length < 2 ^ (prefixWord ++ tailWord_7006587).sum := by decide
  have hdescent : baseEnd_7006587 < baseStart_7006587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006594 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 6]
def baseStart_7006594 : Nat := 118140960795 + 7006594 * 2 ^ 59
def prefixEnd_7006594 : Nat := 4983230072969 + 3 ^ 40 * 7006594 * 2
def baseEnd_7006594 : Nat := 399750052545384989161363

theorem tailTrace_7006594 : CollatzResearch.WordTrace tailWord_7006594 prefixEnd_7006594 399750052545384989161363 := by
  unfold tailWord_7006594
  simp only [CollatzResearch.WordTrace]
  refine ⟨63887869394578510957912709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170367651718876029221100557 63887869394578510957912709)
  ·
    refine ⟨11978975511483470804608633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63887869394578510957912709 11978975511483470804608633)
    ·
      refine ⟨8984231633612603103456475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11978975511483470804608633 8984231633612603103456475)
      ·
        refine ⟨13476347450418904655184713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8984231633612603103456475 13476347450418904655184713)
        ·
          refine ⟨10107260587814178491388535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13476347450418904655184713 10107260587814178491388535)
          ·
            refine ⟨15160890881721267737082803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10107260587814178491388535 15160890881721267737082803)
            ·
              refine ⟨22741336322581901605624205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15160890881721267737082803 22741336322581901605624205)
              ·
                refine ⟨8528001120968213102109077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22741336322581901605624205 8528001120968213102109077)
                ·
                  refine ⟨399750052545384989161363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8528001120968213102109077 399750052545384989161363)
                  ·
                    rfl

theorem cell23_7006594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_7006594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006594 prefixEnd_7006594 := by exact prefixLift 7006594
  have htrace : WordTrace (prefixWord ++ tailWord_7006594) baseStart_7006594 baseEnd_7006594 := by
    simpa [prefixWord, tailWord_7006594, baseEnd_7006594] using wordTrace_append hprefix tailTrace_7006594
  have hstable : (prefixWord ++ tailWord_7006594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006594).length < 2 ^ (prefixWord ++ tailWord_7006594).sum := by decide
  have hdescent : baseEnd_7006594 < baseStart_7006594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006677 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_7006677 : Nat := 118140960795 + 7006677 * 2 ^ 59
def prefixEnd_7006677 : Nat := 4983230072969 + 3 ^ 40 * 7006677 * 2
def baseEnd_7006677 : Nat := 3597793091802788077714385

theorem tailTrace_7006677 : CollatzResearch.WordTrace tailWord_7006677 prefixEnd_7006677 3597793091802788077714385 := by
  unfold tailWord_7006677
  simp only [CollatzResearch.WordTrace]
  refine ⟨255554504837013349006922285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170369669891342232671281523 255554504837013349006922285)
  ·
    refine ⟨95832939313880005877595857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255554504837013349006922285 95832939313880005877595857)
    ·
      refine ⟨71874704485410004408196893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95832939313880005877595857 71874704485410004408196893)
      ·
        refine ⟨26953014182028751653073835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71874704485410004408196893 26953014182028751653073835)
        ·
          refine ⟨40429521273043127479610753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26953014182028751653073835 40429521273043127479610753)
          ·
            refine ⟨30322140954782345609708065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40429521273043127479610753 30322140954782345609708065)
            ·
              refine ⟨22741605716086759207281049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30322140954782345609708065 22741605716086759207281049)
              ·
                refine ⟨17056204287065069405460787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22741605716086759207281049 17056204287065069405460787)
                ·
                  refine ⟨25584306430597604108191181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17056204287065069405460787 25584306430597604108191181)
                  ·
                    refine ⟨9594114911474101540571693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25584306430597604108191181 9594114911474101540571693)
                    ·
                      refine ⟨3597793091802788077714385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9594114911474101540571693 3597793091802788077714385)
                      ·
                        rfl

theorem cell23_7006677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_7006677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006677 prefixEnd_7006677 := by exact prefixLift 7006677
  have htrace : WordTrace (prefixWord ++ tailWord_7006677) baseStart_7006677 baseEnd_7006677 := by
    simpa [prefixWord, tailWord_7006677, baseEnd_7006677] using wordTrace_append hprefix tailTrace_7006677
  have hstable : (prefixWord ++ tailWord_7006677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006677).length < 2 ^ (prefixWord ++ tailWord_7006677).sum := by decide
  have hdescent : baseEnd_7006677 < baseStart_7006677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006721 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_7006721 : Nat := 118140960795 + 7006721 * 2 ^ 59
def prefixEnd_7006721 : Nat := 4983230072969 + 3 ^ 40 * 7006721 * 2
def baseEnd_7006721 : Nat := 3597815684951585905564183

theorem tailTrace_7006721 : CollatzResearch.WordTrace tailWord_7006721 prefixEnd_7006721 3597815684951585905564183 := by
  unfold tailWord_7006721
  simp only [CollatzResearch.WordTrace]
  refine ⟨255556109648853944521524017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170370739765902629681016011 255556109648853944521524017)
  ·
    refine ⟨191667082236640458391143013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255556109648853944521524017 191667082236640458391143013)
    ·
      refine ⟨35937577919370085948339315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191667082236640458391143013 35937577919370085948339315)
      ·
        refine ⟨53906366879055128922508973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35937577919370085948339315 53906366879055128922508973)
        ·
          refine ⟨20214887579645673345940865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53906366879055128922508973 20214887579645673345940865)
          ·
            refine ⟨15161165684734255009455649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20214887579645673345940865 15161165684734255009455649)
            ·
              refine ⟨11370874263550691257091737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15161165684734255009455649 11370874263550691257091737)
              ·
                refine ⟨8528155697663018442818803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11370874263550691257091737 8528155697663018442818803)
                ·
                  refine ⟨12792233546494527664228205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8528155697663018442818803 12792233546494527664228205)
                  ·
                    refine ⟨4797087579935447874085577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12792233546494527664228205 4797087579935447874085577)
                    ·
                      refine ⟨3597815684951585905564183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797087579935447874085577 3597815684951585905564183)
                      ·
                        rfl

theorem cell23_7006721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_7006721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006721 prefixEnd_7006721 := by exact prefixLift 7006721
  have htrace : WordTrace (prefixWord ++ tailWord_7006721) baseStart_7006721 baseEnd_7006721 := by
    simpa [prefixWord, tailWord_7006721, baseEnd_7006721] using wordTrace_append hprefix tailTrace_7006721
  have hstable : (prefixWord ++ tailWord_7006721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006721).length < 2 ^ (prefixWord ++ tailWord_7006721).sum := by decide
  have hdescent : baseEnd_7006721 < baseStart_7006721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006757 : List Nat := [1, 3, 1, 2, 2, 1, 2, 6, 5]
def baseStart_7006757 : Nat := 118140960795 + 7006757 * 2 ^ 59
def prefixEnd_7006757 : Nat := 4983230072969 + 3 ^ 40 * 7006757 * 2
def baseEnd_7006757 : Nat := 399759352250571973857113

theorem tailTrace_7006757 : CollatzResearch.WordTrace tailWord_7006757 prefixEnd_7006757 399759352250571973857113 := by
  unfold tailWord_7006757
  simp only [CollatzResearch.WordTrace]
  refine ⟨255557422676723522669834525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170371615117815681779889683 255557422676723522669834525)
  ·
    refine ⟨95834033503771321001187947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255557422676723522669834525 95834033503771321001187947)
    ·
      refine ⟨143751050255656981501781921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95834033503771321001187947 143751050255656981501781921)
      ·
        refine ⟨107813287691742736126336441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143751050255656981501781921 107813287691742736126336441)
        ·
          refine ⟨80859965768807052094752331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107813287691742736126336441 80859965768807052094752331)
          ·
            refine ⟨121289948653210578142128497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80859965768807052094752331 121289948653210578142128497)
            ·
              refine ⟨90967461489907933606596373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121289948653210578142128497 90967461489907933606596373)
              ·
                refine ⟨4264099757339434387809205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90967461489907933606596373 4264099757339434387809205)
                ·
                  refine ⟨399759352250571973857113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4264099757339434387809205 399759352250571973857113)
                  ·
                    rfl

theorem cell23_7006757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_7006757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006757 prefixEnd_7006757 := by exact prefixLift 7006757
  have htrace : WordTrace (prefixWord ++ tailWord_7006757) baseStart_7006757 baseEnd_7006757 := by
    simpa [prefixWord, tailWord_7006757, baseEnd_7006757] using wordTrace_append hprefix tailTrace_7006757
  have hstable : (prefixWord ++ tailWord_7006757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006757).length < 2 ^ (prefixWord ++ tailWord_7006757).sum := by decide
  have hdescent : baseEnd_7006757 < baseStart_7006757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006770 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_7006770 : Nat := 118140960795 + 7006770 * 2 ^ 59
def prefixEnd_7006770 : Nat := 4983230072969 + 3 ^ 40 * 7006770 * 2
def baseEnd_7006770 : Nat := 1199280281834552071283819

theorem tailTrace_7006770 : CollatzResearch.WordTrace tailWord_7006770 prefixEnd_7006770 1199280281834552071283819 := by
  unfold tailWord_7006770
  simp only [CollatzResearch.WordTrace]
  refine ⟨63889474206419106472514441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170371931217117617260038509 63889474206419106472514441)
  ·
    refine ⟨47917105654814329854385831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63889474206419106472514441 47917105654814329854385831)
    ·
      refine ⟨71875658482221494781578747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47917105654814329854385831 71875658482221494781578747)
      ·
        refine ⟨107813487723332242172368121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71875658482221494781578747 107813487723332242172368121)
        ·
          refine ⟨80860115792499181629276091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107813487723332242172368121 80860115792499181629276091)
          ·
            refine ⟨121290173688748772443914137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80860115792499181629276091 121290173688748772443914137)
            ·
              refine ⟨90967630266561579332935603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121290173688748772443914137 90967630266561579332935603)
              ·
                refine ⟨136451445399842368999403405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90967630266561579332935603 136451445399842368999403405)
                ·
                  refine ⟨51169292024940888374776277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136451445399842368999403405 51169292024940888374776277)
                  ·
                    refine ⟨1199280281834552071283819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51169292024940888374776277 1199280281834552071283819)
                    ·
                      rfl

theorem cell23_7006770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_7006770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006770 prefixEnd_7006770 := by exact prefixLift 7006770
  have htrace : WordTrace (prefixWord ++ tailWord_7006770) baseStart_7006770 baseEnd_7006770 := by
    simpa [prefixWord, tailWord_7006770, baseEnd_7006770] using wordTrace_append hprefix tailTrace_7006770
  have hstable : (prefixWord ++ tailWord_7006770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006770).length < 2 ^ (prefixWord ++ tailWord_7006770).sum := by decide
  have hdescent : baseEnd_7006770 < baseStart_7006770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006772 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7006772 : Nat := 118140960795 + 7006772 * 2 ^ 59
def prefixEnd_7006772 : Nat := 4983230072969 + 3 ^ 40 * 7006772 * 2
def baseEnd_7006772 : Nat := 3597841872464965206026449

theorem tailTrace_7006772 : CollatzResearch.WordTrace tailWord_7006772 prefixEnd_7006772 3597841872464965206026449 := by
  unfold tailWord_7006772
  simp only [CollatzResearch.WordTrace]
  refine ⟨127778984885834590115815285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170371979847779453487753713 127778984885834590115815285)
  ·
    refine ⟨11979279833046992823357683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127778984885834590115815285 11979279833046992823357683)
    ·
      refine ⟨17968919749570489235036525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11979279833046992823357683 17968919749570489235036525)
      ·
        refine ⟨6738344906088933463138697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17968919749570489235036525 6738344906088933463138697)
        ·
          refine ⟨5053758679566700097354023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6738344906088933463138697 5053758679566700097354023)
          ·
            refine ⟨7580638019350050146031035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5053758679566700097354023 7580638019350050146031035)
            ·
              refine ⟨11370957029025075219046553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7580638019350050146031035 11370957029025075219046553)
              ·
                refine ⟨8528217771768806414284915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11370957029025075219046553 8528217771768806414284915)
                ·
                  refine ⟨12792326657653209621427373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8528217771768806414284915 12792326657653209621427373)
                  ·
                    refine ⟨4797122496619953608035265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12792326657653209621427373 4797122496619953608035265)
                    ·
                      refine ⟨3597841872464965206026449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797122496619953608035265 3597841872464965206026449)
                      ·
                        rfl

theorem cell23_7006772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7006772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006772 prefixEnd_7006772 := by exact prefixLift 7006772
  have htrace : WordTrace (prefixWord ++ tailWord_7006772) baseStart_7006772 baseEnd_7006772 := by
    simpa [prefixWord, tailWord_7006772, baseEnd_7006772] using wordTrace_append hprefix tailTrace_7006772
  have hstable : (prefixWord ++ tailWord_7006772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006772).length < 2 ^ (prefixWord ++ tailWord_7006772).sum := by decide
  have hdescent : baseEnd_7006772 < baseStart_7006772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006807 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_7006807 : Nat := 118140960795 + 7006807 * 2 ^ 59
def prefixEnd_7006807 : Nat := 4983230072969 + 3 ^ 40 * 7006807 * 2
def baseEnd_7006807 : Nat := 3597859844287872569088787

theorem tailTrace_7006807 : CollatzResearch.WordTrace tailWord_7006807 prefixEnd_7006807 3597859844287872569088787 := by
  unfold tailWord_7006807
  simp only [CollatzResearch.WordTrace]
  refine ⟨255559246326542381209154675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170372830884361587472769783 255559246326542381209154675)
  ·
    refine ⟨383338869489813571813732013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255559246326542381209154675 383338869489813571813732013)
    ·
      refine ⟨143752076058680089430149505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383338869489813571813732013 143752076058680089430149505)
      ·
        refine ⟨107814057044010067072612129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143752076058680089430149505 107814057044010067072612129)
        ·
          refine ⟨80860542783007550304459097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107814057044010067072612129 80860542783007550304459097)
          ·
            refine ⟨60645407087255662728344323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80860542783007550304459097 60645407087255662728344323)
            ·
              refine ⟨90968110630883494092516485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60645407087255662728344323 90968110630883494092516485)
              ·
                refine ⟨17056520743290655142346841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90968110630883494092516485 17056520743290655142346841)
                ·
                  refine ⟨12792390557467991356760131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17056520743290655142346841 12792390557467991356760131)
                  ·
                    refine ⟨19188585836201987035140197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12792390557467991356760131 19188585836201987035140197)
                    ·
                      refine ⟨3597859844287872569088787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19188585836201987035140197 3597859844287872569088787)
                      ·
                        rfl

theorem cell23_7006807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_7006807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006807 prefixEnd_7006807 := by exact prefixLift 7006807
  have htrace : WordTrace (prefixWord ++ tailWord_7006807) baseStart_7006807 baseEnd_7006807 := by
    simpa [prefixWord, tailWord_7006807, baseEnd_7006807] using wordTrace_append hprefix tailTrace_7006807
  have hstable : (prefixWord ++ tailWord_7006807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006807).length < 2 ^ (prefixWord ++ tailWord_7006807).sum := by decide
  have hdescent : baseEnd_7006807 < baseStart_7006807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006838 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_7006838 : Nat := 118140960795 + 7006838 * 2 ^ 59
def prefixEnd_7006838 : Nat := 4983230072969 + 3 ^ 40 * 7006838 * 2
def baseEnd_7006838 : Nat := 1199291920729387315933715

theorem tailTrace_7006838 : CollatzResearch.WordTrace tailWord_7006838 prefixEnd_7006838 1199291920729387315933715 := by
  unfold tailWord_7006838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15972523561839379593970823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170373584659620049002355445 15972523561839379593970823)
  ·
    refine ⟨23958785342759069390956235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15972523561839379593970823 23958785342759069390956235)
    ·
      refine ⟨35938178014138604086434353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23958785342759069390956235 35938178014138604086434353)
      ·
        refine ⟨26953633510603953064825765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35938178014138604086434353 26953633510603953064825765)
        ·
          refine ⟨5053806283238241199654831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26953633510603953064825765 5053806283238241199654831)
          ·
            refine ⟨7580709424857361799482247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5053806283238241199654831 7580709424857361799482247)
            ·
              refine ⟨11371064137286042699223371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7580709424857361799482247 11371064137286042699223371)
              ·
                refine ⟨17056596205929064048835057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11371064137286042699223371 17056596205929064048835057)
                ·
                  refine ⟨12792447154446798036626293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17056596205929064048835057 12792447154446798036626293)
                  ·
                    refine ⟨1199291920729387315933715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12792447154446798036626293 1199291920729387315933715)
                    ·
                      rfl

theorem cell23_7006838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_7006838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006838 prefixEnd_7006838 := by exact prefixLift 7006838
  have htrace : WordTrace (prefixWord ++ tailWord_7006838) baseStart_7006838 baseEnd_7006838 := by
    simpa [prefixWord, tailWord_7006838, baseEnd_7006838] using wordTrace_append hprefix tailTrace_7006838
  have hstable : (prefixWord ++ tailWord_7006838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006838).length < 2 ^ (prefixWord ++ tailWord_7006838).sum := by decide
  have hdescent : baseEnd_7006838 < baseStart_7006838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006844 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_7006844 : Nat := 118140960795 + 7006844 * 2 ^ 59
def prefixEnd_7006844 : Nat := 4983230072969 + 3 ^ 40 * 7006844 * 2
def baseEnd_7006844 : Nat := 3597878843072088924326117

theorem tailTrace_7006844 : CollatzResearch.WordTrace tailWord_7006844 prefixEnd_7006844 3597878843072088924326117 := by
  unfold tailWord_7006844
  simp only [CollatzResearch.WordTrace]
  refine ⟨127780297913704168264125793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170373730551605557685501057 127780297913704168264125793)
  ·
    refine ⟨95835223435278126198094345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127780297913704168264125793 95835223435278126198094345)
    ·
      refine ⟨71876417576458594648570759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95835223435278126198094345 71876417576458594648570759)
      ·
        refine ⟨107814626364687891972856139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71876417576458594648570759 107814626364687891972856139)
        ·
          refine ⟨161721939547031837959284209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107814626364687891972856139 161721939547031837959284209)
          ·
            refine ⟨121291454660273878469463157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161721939547031837959284209 121291454660273878469463157)
            ·
              refine ⟨11371073874400676106512171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121291454660273878469463157 11371073874400676106512171)
              ·
                refine ⟨17056610811601014159768257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11371073874400676106512171 17056610811601014159768257)
                ·
                  refine ⟨12792458108700760619826193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17056610811601014159768257 12792458108700760619826193)
                  ·
                    refine ⟨9594343581525570464869645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12792458108700760619826193 9594343581525570464869645)
                    ·
                      refine ⟨3597878843072088924326117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9594343581525570464869645 3597878843072088924326117)
                      ·
                        rfl

theorem cell23_7006844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_7006844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006844 prefixEnd_7006844 := by exact prefixLift 7006844
  have htrace : WordTrace (prefixWord ++ tailWord_7006844) baseStart_7006844 baseEnd_7006844 := by
    simpa [prefixWord, tailWord_7006844, baseEnd_7006844] using wordTrace_append hprefix tailTrace_7006844
  have hstable : (prefixWord ++ tailWord_7006844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006844).length < 2 ^ (prefixWord ++ tailWord_7006844).sum := by decide
  have hdescent : baseEnd_7006844 < baseStart_7006844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006868 : List Nat := [2, 4, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_7006868 : Nat := 118140960795 + 7006868 * 2 ^ 59
def prefixEnd_7006868 : Nat := 4983230072969 + 3 ^ 40 * 7006868 * 2
def baseEnd_7006868 : Nat := 1199297055535932276808669

theorem tailTrace_7006868 : CollatzResearch.WordTrace tailWord_7006868 prefixEnd_7006868 1199297055535932276808669 := by
  unfold tailWord_7006868
  simp only [CollatzResearch.WordTrace]
  refine ⟨127780735589660694313562629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170374314119547592418083505 127780735589660694313562629)
  ·
    refine ⟨23958887923061380183792993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127780735589660694313562629 23958887923061380183792993)
    ·
      refine ⟨17969165942296035137844745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23958887923061380183792993 17969165942296035137844745)
      ·
        refine ⟨13476874456722026353383559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17969165942296035137844745 13476874456722026353383559)
        ·
          refine ⟨20215311685083039530075339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13476874456722026353383559 20215311685083039530075339)
          ·
            refine ⟨30322967527624559295113009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20215311685083039530075339 30322967527624559295113009)
            ·
              refine ⟨22742225645718419471334757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30322967527624559295113009 22742225645718419471334757)
              ·
                refine ⟨4264167308572203650875267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22742225645718419471334757 4264167308572203650875267)
                ·
                  refine ⟨6396250962858305476312901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264167308572203650875267 6396250962858305476312901)
                  ·
                    refine ⟨1199297055535932276808669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6396250962858305476312901 1199297055535932276808669)
                    ·
                      rfl

theorem cell23_7006868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_7006868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006868 prefixEnd_7006868 := by exact prefixLift 7006868
  have htrace : WordTrace (prefixWord ++ tailWord_7006868) baseStart_7006868 baseEnd_7006868 := by
    simpa [prefixWord, tailWord_7006868, baseEnd_7006868] using wordTrace_append hprefix tailTrace_7006868
  have hstable : (prefixWord ++ tailWord_7006868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006868).length < 2 ^ (prefixWord ++ tailWord_7006868).sum := by decide
  have hdescent : baseEnd_7006868 < baseStart_7006868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006877 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_7006877 : Nat := 118140960795 + 7006877 * 2 ^ 59
def prefixEnd_7006877 : Nat := 4983230072969 + 3 ^ 40 * 7006877 * 2
def baseEnd_7006877 : Nat := 1199298595977895765071155

theorem tailTrace_7006877 : CollatzResearch.WordTrace tailWord_7006877 prefixEnd_7006877 1199298595977895765071155 := by
  unfold tailWord_7006877
  simp only [CollatzResearch.WordTrace]
  refine ⟨255561799436288783164202885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170374532957525855442801923 255561799436288783164202885)
  ·
    refine ⟨47917837394304146843288041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255561799436288783164202885 47917837394304146843288041)
    ·
      refine ⟨35938378045728110132466031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47917837394304146843288041 35938378045728110132466031)
      ·
        refine ⟨53907567068592165198699047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35938378045728110132466031 53907567068592165198699047)
        ·
          refine ⟨80861350602888247798048571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53907567068592165198699047 80861350602888247798048571)
          ·
            refine ⟨121292025904332371697072857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80861350602888247798048571 121292025904332371697072857)
            ·
              refine ⟨90969019428249278772804643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121292025904332371697072857 90969019428249278772804643)
              ·
                refine ⟨136453529142373918159206965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90969019428249278772804643 136453529142373918159206965)
                ·
                  refine ⟨12792518357097554827425653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136453529142373918159206965 12792518357097554827425653)
                  ·
                    refine ⟨1199298595977895765071155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12792518357097554827425653 1199298595977895765071155)
                    ·
                      rfl

theorem cell23_7006877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_7006877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006877 prefixEnd_7006877 := by exact prefixLift 7006877
  have htrace : WordTrace (prefixWord ++ tailWord_7006877) baseStart_7006877 baseEnd_7006877 := by
    simpa [prefixWord, tailWord_7006877, baseEnd_7006877] using wordTrace_append hprefix tailTrace_7006877
  have hstable : (prefixWord ++ tailWord_7006877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006877).length < 2 ^ (prefixWord ++ tailWord_7006877).sum := by decide
  have hdescent : baseEnd_7006877 < baseStart_7006877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006881 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 6]
def baseStart_7006881 : Nat := 118140960795 + 7006881 * 2 ^ 59
def prefixEnd_7006881 : Nat := 4983230072969 + 3 ^ 40 * 7006881 * 2
def baseEnd_7006881 : Nat := 399766426872922808840383

theorem tailTrace_7006881 : CollatzResearch.WordTrace tailWord_7006881 prefixEnd_7006881 399766426872922808840383 := by
  unfold tailWord_7006881
  simp only [CollatzResearch.WordTrace]
  refine ⟨255561945328274291847348497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170374630218849527898232331 255561945328274291847348497)
  ·
    refine ⟨191671458996205718885511373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255561945328274291847348497 191671458996205718885511373)
    ·
      refine ⟨71876797123577144582066765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191671458996205718885511373 71876797123577144582066765)
      ·
        refine ⟨26953798921341429218275037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71876797123577144582066765 26953798921341429218275037)
        ·
          refine ⟨10107674595503035956853139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26953798921341429218275037 10107674595503035956853139)
          ·
            refine ⟨15161511893254553935279709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10107674595503035956853139 15161511893254553935279709)
            ·
              refine ⟨5685566959970457725729891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15161511893254553935279709 5685566959970457725729891)
              ·
                refine ⟨8528350439955686588594837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5685566959970457725729891 8528350439955686588594837)
                ·
                  refine ⟨399766426872922808840383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8528350439955686588594837 399766426872922808840383)
                  ·
                    rfl

theorem cell23_7006881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 6].length) (baseStart_7006881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006881 prefixEnd_7006881 := by exact prefixLift 7006881
  have htrace : WordTrace (prefixWord ++ tailWord_7006881) baseStart_7006881 baseEnd_7006881 := by
    simpa [prefixWord, tailWord_7006881, baseEnd_7006881] using wordTrace_append hprefix tailTrace_7006881
  have hstable : (prefixWord ++ tailWord_7006881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006881).length < 2 ^ (prefixWord ++ tailWord_7006881).sum := by decide
  have hdescent : baseEnd_7006881 < baseStart_7006881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006884 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_7006884 : Nat := 118140960795 + 7006884 * 2 ^ 59
def prefixEnd_7006884 : Nat := 4983230072969 + 3 ^ 40 * 7006884 * 2
def baseEnd_7006884 : Nat := 3597899382298268767825933

theorem tailTrace_7006884 : CollatzResearch.WordTrace tailWord_7006884 prefixEnd_7006884 3597899382298268767825933 := by
  unfold tailWord_7006884
  simp only [CollatzResearch.WordTrace]
  refine ⟨127781027373631711679853853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170374703164842282239805137 127781027373631711679853853)
  ·
    refine ⟨47917885265111891879945195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127781027373631711679853853 47917885265111891879945195)
    ·
      refine ⟨71876827897667837819917793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47917885265111891879945195 71876827897667837819917793)
      ·
        refine ⟨53907620923250878364938345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71876827897667837819917793 53907620923250878364938345)
        ·
          refine ⟨40430715692438158773703759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53907620923250878364938345 40430715692438158773703759)
          ·
            refine ⟨60646073538657238160555639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40430715692438158773703759 60646073538657238160555639)
            ·
              refine ⟨90969110307985857240833459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60646073538657238160555639 90969110307985857240833459)
              ·
                refine ⟨136453665461978785861250189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90969110307985857240833459 136453665461978785861250189)
                ·
                  refine ⟨51170124548242044697968821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136453665461978785861250189 51170124548242044697968821)
                  ·
                    refine ⟨4797199176397691690434577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51170124548242044697968821 4797199176397691690434577)
                    ·
                      refine ⟨3597899382298268767825933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797199176397691690434577 3597899382298268767825933)
                      ·
                        rfl

theorem cell23_7006884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_7006884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006884 prefixEnd_7006884 := by exact prefixLift 7006884
  have htrace : WordTrace (prefixWord ++ tailWord_7006884) baseStart_7006884 baseEnd_7006884 := by
    simpa [prefixWord, tailWord_7006884, baseEnd_7006884] using wordTrace_append hprefix tailTrace_7006884
  have hstable : (prefixWord ++ tailWord_7006884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006884).length < 2 ^ (prefixWord ++ tailWord_7006884).sum := by decide
  have hdescent : baseEnd_7006884 < baseStart_7006884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006901 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_7006901 : Nat := 118140960795 + 7006901 * 2 ^ 59
def prefixEnd_7006901 : Nat := 4983230072969 + 3 ^ 40 * 7006901 * 2
def baseEnd_7006901 : Nat := 3597908111469395201313355

theorem tailTrace_7006901 : CollatzResearch.WordTrace tailWord_7006901 prefixEnd_7006901 3597908111469395201313355 := by
  unfold tailWord_7006901
  simp only [CollatzResearch.WordTrace]
  refine ⟨255562674788201835263076557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170375116525467890175384371 255562674788201835263076557)
  ·
    refine ⟨95836003045575688223653709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255562674788201835263076557 95836003045575688223653709)
    ·
      refine ⟨35938501142090883083870141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95836003045575688223653709 35938501142090883083870141)
      ·
        refine ⟨13476937928284081156451303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35938501142090883083870141 13476937928284081156451303)
        ·
          refine ⟨20215406892426121734676955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13476937928284081156451303 20215406892426121734676955)
          ·
            refine ⟨30323110338639182602015433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20215406892426121734676955 30323110338639182602015433)
            ·
              refine ⟨22742332753979386951511575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30323110338639182602015433 22742332753979386951511575)
              ·
                refine ⟨34113499130969080427267363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22742332753979386951511575 34113499130969080427267363)
                ·
                  refine ⟨51170248696453620640901045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34113499130969080427267363 51170248696453620640901045)
                  ·
                    refine ⟨4797210815292526935084473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51170248696453620640901045 4797210815292526935084473)
                    ·
                      refine ⟨3597908111469395201313355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797210815292526935084473 3597908111469395201313355)
                      ·
                        rfl

theorem cell23_7006901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_7006901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006901 prefixEnd_7006901 := by exact prefixLift 7006901
  have htrace : WordTrace (prefixWord ++ tailWord_7006901) baseStart_7006901 baseEnd_7006901 := by
    simpa [prefixWord, tailWord_7006901, baseEnd_7006901] using wordTrace_append hprefix tailTrace_7006901
  have hstable : (prefixWord ++ tailWord_7006901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006901).length < 2 ^ (prefixWord ++ tailWord_7006901).sum := by decide
  have hdescent : baseEnd_7006901 < baseStart_7006901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006902 : List Nat := [5, 1, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_7006902 : Nat := 118140960795 + 7006902 * 2 ^ 59
def prefixEnd_7006902 : Nat := 4983230072969 + 3 ^ 40 * 7006902 * 2
def baseEnd_7006902 : Nat := 1199302874983349899133617

theorem tailTrace_7006902 : CollatzResearch.WordTrace tailWord_7006902 prefixEnd_7006902 1199302874983349899133617 := by
  unfold tailWord_7006902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15972669453824888277116435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170375140840798808289241973 15972669453824888277116435)
  ·
    refine ⟨23959004180737332415674653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15972669453824888277116435 23959004180737332415674653)
    ·
      refine ⟨8984626567776499655877995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23959004180737332415674653 8984626567776499655877995)
      ·
        refine ⟨13476939851664749483816993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8984626567776499655877995 13476939851664749483816993)
        ·
          refine ⟨10107704888748562112862745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13476939851664749483816993 10107704888748562112862745)
          ·
            refine ⟨7580778666561421584647059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10107704888748562112862745 7580778666561421584647059)
            ·
              refine ⟨11371167999842132376970589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7580778666561421584647059 11371167999842132376970589)
              ·
                refine ⟨4264187999940799641363971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11371167999842132376970589 4264187999940799641363971)
                ·
                  refine ⟨6396281999911199462045957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264187999940799641363971 6396281999911199462045957)
                  ·
                    refine ⟨1199302874983349899133617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6396281999911199462045957 1199302874983349899133617)
                    ·
                      rfl

theorem cell23_7006902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_7006902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006902 prefixEnd_7006902 := by exact prefixLift 7006902
  have htrace : WordTrace (prefixWord ++ tailWord_7006902) baseStart_7006902 baseEnd_7006902 := by
    simpa [prefixWord, tailWord_7006902, baseEnd_7006902] using wordTrace_append hprefix tailTrace_7006902
  have hstable : (prefixWord ++ tailWord_7006902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006902).length < 2 ^ (prefixWord ++ tailWord_7006902).sum := by decide
  have hdescent : baseEnd_7006902 < baseStart_7006902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7006937 : List Nat := [1, 2, 1, 2, 3, 2, 4, 8]
def baseStart_7006937 : Nat := 118140960795 + 7006937 * 2 ^ 59
def prefixEnd_7006937 : Nat := 4983230072969 + 3 ^ 40 * 7006937 * 2
def baseEnd_7006937 : Nat := 133256540621220631869007

theorem tailTrace_7006937 : CollatzResearch.WordTrace tailWord_7006937 prefixEnd_7006937 133256540621220631869007 := by
  unfold tailWord_7006937
  simp only [CollatzResearch.WordTrace]
  refine ⟨255563987816071413411387065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170375991877380942274258043 255563987816071413411387065)
  ·
    refine ⟨191672990862053560058540299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255563987816071413411387065 191672990862053560058540299)
    ·
      refine ⟨287509486293080340087810449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191672990862053560058540299 287509486293080340087810449)
      ·
        refine ⟨215632114719810255065857837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287509486293080340087810449 215632114719810255065857837)
        ·
          refine ⟨80862043019928845649696689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215632114719810255065857837 80862043019928845649696689)
          ·
            refine ⟨60646532264946634237272517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80862043019928845649696689 60646532264946634237272517)
            ·
              refine ⟨11371224799677493919488597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60646532264946634237272517 11371224799677493919488597)
              ·
                refine ⟨133256540621220631869007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11371224799677493919488597 133256540621220631869007)
                ·
                  rfl

theorem cell23_7006937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 8].length) (baseStart_7006937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7006937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7006937 prefixEnd_7006937 := by exact prefixLift 7006937
  have htrace : WordTrace (prefixWord ++ tailWord_7006937) baseStart_7006937 baseEnd_7006937 := by
    simpa [prefixWord, tailWord_7006937, baseEnd_7006937] using wordTrace_append hprefix tailTrace_7006937
  have hstable : (prefixWord ++ tailWord_7006937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7006937).length < 2 ^ (prefixWord ++ tailWord_7006937).sum := by decide
  have hdescent : baseEnd_7006937 < baseStart_7006937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7006937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007084 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_7007084 : Nat := 118140960795 + 7007084 * 2 ^ 59
def prefixEnd_7007084 : Nat := 4983230072969 + 3 ^ 40 * 7007084 * 2
def baseEnd_7007084 : Nat := 3598002078429167985325013

theorem tailTrace_7007084 : CollatzResearch.WordTrace tailWord_7007084 prefixEnd_7007084 3598002078429167985325013 := by
  unfold tailWord_7007084
  simp only [CollatzResearch.WordTrace]
  refine ⟨127784674673269428758494153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170379566231025905011325537 127784674673269428758494153)
  ·
    refine ⟨95838506004952071568870615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127784674673269428758494153 95838506004952071568870615)
    ·
      refine ⟨143757759007428107353305923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95838506004952071568870615 143757759007428107353305923)
      ·
        refine ⟨215636638511142161029958885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143757759007428107353305923 215636638511142161029958885)
        ·
          refine ⟨40431869720839155193117291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215636638511142161029958885 40431869720839155193117291)
          ·
            refine ⟨60647804581258732789675937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40431869720839155193117291 60647804581258732789675937)
            ·
              refine ⟨45485853435944049592256953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60647804581258732789675937 45485853435944049592256953)
              ·
                refine ⟨34114390076958037194192715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45485853435944049592256953 34114390076958037194192715)
                ·
                  refine ⟨51171585115437055791289073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34114390076958037194192715 51171585115437055791289073)
                  ·
                    refine ⟨38378688836577791843466805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51171585115437055791289073 38378688836577791843466805)
                    ·
                      refine ⟨3598002078429167985325013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38378688836577791843466805 3598002078429167985325013)
                      ·
                        rfl

theorem cell23_7007084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_7007084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007084 prefixEnd_7007084 := by exact prefixLift 7007084
  have htrace : WordTrace (prefixWord ++ tailWord_7007084) baseStart_7007084 baseEnd_7007084 := by
    simpa [prefixWord, tailWord_7007084, baseEnd_7007084] using wordTrace_append hprefix tailTrace_7007084
  have hstable : (prefixWord ++ tailWord_7007084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007084).length < 2 ^ (prefixWord ++ tailWord_7007084).sum := by decide
  have hdescent : baseEnd_7007084 < baseStart_7007084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007171 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 3, 5, 2]
def baseStart_7007171 : Nat := 118140960795 + 7007171 * 2 ^ 59
def prefixEnd_7007171 : Nat := 4983230072969 + 3 ^ 40 * 7007171 * 2
def baseEnd_7007171 : Nat := 3598046751246109144937113

theorem tailTrace_7007171 : CollatzResearch.WordTrace tailWord_7007171 prefixEnd_7007171 3598046751246109144937113 := by
  unfold tailWord_7007171
  simp only [CollatzResearch.WordTrace]
  refine ⟨255572522497223671375405367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170381681664815780916936911 255572522497223671375405367)
  ·
    refine ⟨383358783745835507063108051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255572522497223671375405367 383358783745835507063108051)
    ·
      refine ⟨575038175618753260594662077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383358783745835507063108051 575038175618753260594662077)
      ·
        refine ⟨215639315857032472722998279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575038175618753260594662077 215639315857032472722998279)
        ·
          refine ⟨323458973785548709084497419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215639315857032472722998279 323458973785548709084497419)
          ·
            refine ⟨485188460678323063626746129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323458973785548709084497419 485188460678323063626746129)
            ·
              refine ⟨363891345508742297720059597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485188460678323063626746129 363891345508742297720059597)
              ·
                refine ⟨136459254565778361645022349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363891345508742297720059597 136459254565778361645022349)
                ·
                  refine ⟨51172220462166885616883381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136459254565778361645022349 51172220462166885616883381)
                  ·
                    refine ⟨4797395668328145526582817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51172220462166885616883381 4797395668328145526582817)
                    ·
                      refine ⟨3598046751246109144937113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797395668328145526582817 3598046751246109144937113)
                      ·
                        rfl

theorem cell23_7007171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_7007171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007171 prefixEnd_7007171 := by exact prefixLift 7007171
  have htrace : WordTrace (prefixWord ++ tailWord_7007171) baseStart_7007171 baseEnd_7007171 := by
    simpa [prefixWord, tailWord_7007171, baseEnd_7007171] using wordTrace_append hprefix tailTrace_7007171
  have hstable : (prefixWord ++ tailWord_7007171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007171).length < 2 ^ (prefixWord ++ tailWord_7007171).sum := by decide
  have hdescent : baseEnd_7007171 < baseStart_7007171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007224 : List Nat := [2, 1, 2, 1, 1, 3, 1, 12]
def baseStart_7007224 : Nat := 118140960795 + 7007224 * 2 ^ 59
def prefixEnd_7007224 : Nat := 4983230072969 + 3 ^ 40 * 7007224 * 2
def baseEnd_7007224 : Nat := 133261998730399905095347

theorem tailTrace_7007224 : CollatzResearch.WordTrace tailWord_7007224 prefixEnd_7007224 133261998730399905095347 := by
  unfold tailWord_7007224
  simp only [CollatzResearch.WordTrace]
  refine ⟨127787227783015830713542363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170382970377354440951389817 127787227783015830713542363)
  ·
    refine ⟨191680841674523746070313545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127787227783015830713542363 191680841674523746070313545)
    ·
      refine ⟨143760631255892809552735159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191680841674523746070313545 143760631255892809552735159)
      ·
        refine ⟨215640946883839214329102739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143760631255892809552735159 215640946883839214329102739)
        ·
          refine ⟨323461420325758821493654109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215640946883839214329102739 323461420325758821493654109)
          ·
            refine ⟨121298032622159558060120291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323461420325758821493654109 121298032622159558060120291)
            ·
              refine ⟨181947048933239337090180437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121298032622159558060120291 181947048933239337090180437)
              ·
                refine ⟨133261998730399905095347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 181947048933239337090180437 133261998730399905095347)
                ·
                  rfl

theorem cell23_7007224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 12].length) (baseStart_7007224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007224 prefixEnd_7007224 := by exact prefixLift 7007224
  have htrace : WordTrace (prefixWord ++ tailWord_7007224) baseStart_7007224 baseEnd_7007224 := by
    simpa [prefixWord, tailWord_7007224, baseEnd_7007224] using wordTrace_append hprefix tailTrace_7007224
  have hstable : (prefixWord ++ tailWord_7007224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007224).length < 2 ^ (prefixWord ++ tailWord_7007224).sum := by decide
  have hdescent : baseEnd_7007224 < baseStart_7007224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007228 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_7007228 : Nat := 118140960795 + 7007228 * 2 ^ 59
def prefixEnd_7007228 : Nat := 4983230072969 + 3 ^ 40 * 7007228 * 2
def baseEnd_7007228 : Nat := 1199358673214471807308117

theorem tailTrace_7007228 : CollatzResearch.WordTrace tailWord_7007228 prefixEnd_7007228 1199358673214471807308117 := by
  unfold tailWord_7007228
  simp only [CollatzResearch.WordTrace]
  refine ⟨127787300729008585055115169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170383067638678113406820225 127787300729008585055115169)
  ·
    refine ⟨95840475546756438791336377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127787300729008585055115169 95840475546756438791336377)
    ·
      refine ⟨71880356660067329093502283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95840475546756438791336377 71880356660067329093502283)
      ·
        refine ⟨107820534990100993640253425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71880356660067329093502283 107820534990100993640253425)
        ·
          refine ⟨80865401242575745230190069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107820534990100993640253425 80865401242575745230190069)
          ·
            refine ⟨7581131366491476115330319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80865401242575745230190069 7581131366491476115330319)
            ·
              refine ⟨11371697049737214172995479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581131366491476115330319 11371697049737214172995479)
              ·
                refine ⟨17057545574605821259493219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11371697049737214172995479 17057545574605821259493219)
                ·
                  refine ⟨25586318361908731889239829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17057545574605821259493219 25586318361908731889239829)
                  ·
                    refine ⟨1199358673214471807308117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25586318361908731889239829 1199358673214471807308117)
                    ·
                      rfl

theorem cell23_7007228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_7007228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007228 prefixEnd_7007228 := by exact prefixLift 7007228
  have htrace : WordTrace (prefixWord ++ tailWord_7007228) baseStart_7007228 baseEnd_7007228 := by
    simpa [prefixWord, tailWord_7007228, baseEnd_7007228] using wordTrace_append hprefix tailTrace_7007228
  have hstable : (prefixWord ++ tailWord_7007228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007228).length < 2 ^ (prefixWord ++ tailWord_7007228).sum := by decide
  have hdescent : baseEnd_7007228 < baseStart_7007228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007251 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 3]
def baseStart_7007251 : Nat := 118140960795 + 7007251 * 2 ^ 59
def prefixEnd_7007251 : Nat := 4983230072969 + 3 ^ 40 * 7007251 * 2
def baseEnd_7007251 : Nat := 3598087829698468831936745

theorem tailTrace_7007251 : CollatzResearch.WordTrace tailWord_7007251 prefixEnd_7007251 3598087829698468831936745 := by
  unfold tailWord_7007251
  simp only [CollatzResearch.WordTrace]
  refine ⟨255575440336933845038317607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170383626891289230025545071 255575440336933845038317607)
  ·
    refine ⟨383363160505400767557476411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255575440336933845038317607 383363160505400767557476411)
    ·
      refine ⟨575044740758101151336214617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383363160505400767557476411 575044740758101151336214617)
      ·
        refine ⟨431283555568575863502160963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575044740758101151336214617 431283555568575863502160963)
        ·
          refine ⟨646925333352863795253241445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431283555568575863502160963 646925333352863795253241445)
          ·
            refine ⟨121298500003661961609982771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 646925333352863795253241445 121298500003661961609982771)
            ·
              refine ⟨181947750005492942414974157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121298500003661961609982771 181947750005492942414974157)
              ·
                refine ⟨68230406252059853405615309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181947750005492942414974157 68230406252059853405615309)
                ·
                  refine ⟨25586402344522445027105741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68230406252059853405615309 25586402344522445027105741)
                  ·
                    refine ⟨9594900879195916885164653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25586402344522445027105741 9594900879195916885164653)
                    ·
                      refine ⟨3598087829698468831936745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9594900879195916885164653 3598087829698468831936745)
                      ·
                        rfl

theorem cell23_7007251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_7007251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007251 prefixEnd_7007251 := by exact prefixLift 7007251
  have htrace : WordTrace (prefixWord ++ tailWord_7007251) baseStart_7007251 baseEnd_7007251 := by
    simpa [prefixWord, tailWord_7007251, baseEnd_7007251] using wordTrace_append hprefix tailTrace_7007251
  have hstable : (prefixWord ++ tailWord_7007251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007251).length < 2 ^ (prefixWord ++ tailWord_7007251).sum := by decide
  have hdescent : baseEnd_7007251 < baseStart_7007251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007255 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7007255 : Nat := 118140960795 + 7007255 * 2 ^ 59
def prefixEnd_7007255 : Nat := 4983230072969 + 3 ^ 40 * 7007255 * 2
def baseEnd_7007255 : Nat := 3598089883621086816286727

theorem tailTrace_7007255 : CollatzResearch.WordTrace tailWord_7007255 prefixEnd_7007255 3598089883621086816286727 := by
  unfold tailWord_7007255
  simp only [CollatzResearch.WordTrace]
  refine ⟨255575586228919353721463219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170383724152612902480975479 255575586228919353721463219)
  ·
    refine ⟨383363379343379030582194829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255575586228919353721463219 383363379343379030582194829)
    ·
      refine ⟨143761267253767136468323061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383363379343379030582194829 143761267253767136468323061)
      ·
        refine ⟨13477618805040669043905287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143761267253767136468323061 13477618805040669043905287)
        ·
          refine ⟨20216428207561003565857931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13477618805040669043905287 20216428207561003565857931)
          ·
            refine ⟨30324642311341505348786897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20216428207561003565857931 30324642311341505348786897)
            ·
              refine ⟨22743481733506129011590173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30324642311341505348786897 22743481733506129011590173)
              ·
                refine ⟨8528805650064798379346315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22743481733506129011590173 8528805650064798379346315)
                ·
                  refine ⟨12793208475097197569019473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8528805650064798379346315 12793208475097197569019473)
                  ·
                    refine ⟨9594906356322898176764605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12793208475097197569019473 9594906356322898176764605)
                    ·
                      refine ⟨3598089883621086816286727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9594906356322898176764605 3598089883621086816286727)
                      ·
                        rfl

theorem cell23_7007255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7007255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007255 prefixEnd_7007255 := by exact prefixLift 7007255
  have htrace : WordTrace (prefixWord ++ tailWord_7007255) baseStart_7007255 baseEnd_7007255 := by
    simpa [prefixWord, tailWord_7007255, baseEnd_7007255] using wordTrace_append hprefix tailTrace_7007255
  have hstable : (prefixWord ++ tailWord_7007255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007255).length < 2 ^ (prefixWord ++ tailWord_7007255).sum := by decide
  have hdescent : baseEnd_7007255 < baseStart_7007255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007269 : List Nat := [1, 3, 1, 2, 2, 2, 5, 2, 1, 2, 2]
def baseStart_7007269 : Nat := 118140960795 + 7007269 * 2 ^ 59
def prefixEnd_7007269 : Nat := 4983230072969 + 3 ^ 40 * 7007269 * 2
def baseEnd_7007269 : Nat := 3598097072350249761511663

theorem tailTrace_7007269 : CollatzResearch.WordTrace tailWord_7007269 prefixEnd_7007269 3598097072350249761511663 := by
  unfold tailWord_7007269
  simp only [CollatzResearch.WordTrace]
  refine ⟨255576096850868634112472861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170384064567245756074981907 255576096850868634112472861)
  ·
    refine ⟨95841036319075737792177323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255576096850868634112472861 95841036319075737792177323)
    ·
      refine ⟨143761554478613606688265985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95841036319075737792177323 143761554478613606688265985)
      ·
        refine ⟨107821165858960205016199489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143761554478613606688265985 107821165858960205016199489)
        ·
          refine ⟨80865874394220153762149617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107821165858960205016199489 80865874394220153762149617)
          ·
            refine ⟨60649405795665115321612213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80865874394220153762149617 60649405795665115321612213)
            ·
              refine ⟨5685881793343604561401145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60649405795665115321612213 5685881793343604561401145)
              ·
                refine ⟨4264411345007703421050859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5685881793343604561401145 4264411345007703421050859)
                ·
                  refine ⟨6396617017511555131576289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264411345007703421050859 6396617017511555131576289)
                  ·
                    refine ⟨4797462763133666348682217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6396617017511555131576289 4797462763133666348682217)
                    ·
                      refine ⟨3598097072350249761511663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797462763133666348682217 3598097072350249761511663)
                      ·
                        rfl

theorem cell23_7007269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_7007269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007269 prefixEnd_7007269 := by exact prefixLift 7007269
  have htrace : WordTrace (prefixWord ++ tailWord_7007269) baseStart_7007269 baseEnd_7007269 := by
    simpa [prefixWord, tailWord_7007269, baseEnd_7007269] using wordTrace_append hprefix tailTrace_7007269
  have hstable : (prefixWord ++ tailWord_7007269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007269).length < 2 ^ (prefixWord ++ tailWord_7007269).sum := by decide
  have hdescent : baseEnd_7007269 < baseStart_7007269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007302 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_7007302 : Nat := 118140960795 + 7007302 * 2 ^ 59
def prefixEnd_7007302 : Nat := 4983230072969 + 3 ^ 40 * 7007302 * 2
def baseEnd_7007302 : Nat := 3598114017211848132399011

theorem tailTrace_7007302 : CollatzResearch.WordTrace tailWord_7007302 prefixEnd_7007302 3598114017211848132399011 := by
  unfold tailWord_7007302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7986790639367158773388255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170384866973166053832282773 7986790639367158773388255)
  ·
    refine ⟨11980185959050738160082383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7986790639367158773388255 11980185959050738160082383)
    ·
      refine ⟨17970278938576107240123575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11980185959050738160082383 17970278938576107240123575)
      ·
        refine ⟨26955418407864160860185363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17970278938576107240123575 26955418407864160860185363)
        ·
          refine ⟨40433127611796241290278045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26955418407864160860185363 40433127611796241290278045)
          ·
            refine ⟨15162422854423590483854267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40433127611796241290278045 15162422854423590483854267)
            ·
              refine ⟨22743634281635385725781401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15162422854423590483854267 22743634281635385725781401)
              ·
                refine ⟨17057725711226539294336051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22743634281635385725781401 17057725711226539294336051)
                ·
                  refine ⟨25586588566839808941504077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17057725711226539294336051 25586588566839808941504077)
                  ·
                    refine ⟨9594970712564928353064029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25586588566839808941504077 9594970712564928353064029)
                    ·
                      refine ⟨3598114017211848132399011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9594970712564928353064029 3598114017211848132399011)
                      ·
                        rfl

theorem cell23_7007302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_7007302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007302 prefixEnd_7007302 := by exact prefixLift 7007302
  have htrace : WordTrace (prefixWord ++ tailWord_7007302) baseStart_7007302 baseEnd_7007302 := by
    simpa [prefixWord, tailWord_7007302, baseEnd_7007302] using wordTrace_append hprefix tailTrace_7007302
  have hstable : (prefixWord ++ tailWord_7007302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007302).length < 2 ^ (prefixWord ++ tailWord_7007302).sum := by decide
  have hdescent : baseEnd_7007302 < baseStart_7007302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007311 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 3]
def baseStart_7007311 : Nat := 118140960795 + 7007311 * 2 ^ 59
def prefixEnd_7007311 : Nat := 4983230072969 + 3 ^ 40 * 7007311 * 2
def baseEnd_7007311 : Nat := 3598118638537738597186469

theorem tailTrace_7007311 : CollatzResearch.WordTrace tailWord_7007311 prefixEnd_7007311 3598118638537738597186469 := by
  unfold tailWord_7007311
  simp only [CollatzResearch.WordTrace]
  refine ⟨255577628716716475285501787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170385085811144316857001191 255577628716716475285501787)
  ·
    refine ⟨383366443075074712928252681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255577628716716475285501787 383366443075074712928252681)
    ·
      refine ⟨287524832306306034696189511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383366443075074712928252681 287524832306306034696189511)
      ·
        refine ⟨431287248459459052044284267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287524832306306034696189511 431287248459459052044284267)
        ·
          refine ⟨646930872689188578066426401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431287248459459052044284267 646930872689188578066426401)
          ·
            refine ⟨485198154516891433549819801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646930872689188578066426401 485198154516891433549819801)
            ·
              refine ⟨363898615887668575162364851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485198154516891433549819801 363898615887668575162364851)
              ·
                refine ⟨545847923831502862743547277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363898615887668575162364851 545847923831502862743547277)
                ·
                  refine ⟨204692971436813573528830229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545847923831502862743547277 204692971436813573528830229)
                  ·
                    refine ⟨9594983036100636259163917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 204692971436813573528830229 9594983036100636259163917)
                    ·
                      refine ⟨3598118638537738597186469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9594983036100636259163917 3598118638537738597186469)
                      ·
                        rfl

theorem cell23_7007311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_7007311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007311 prefixEnd_7007311 := by exact prefixLift 7007311
  have htrace : WordTrace (prefixWord ++ tailWord_7007311) baseStart_7007311 baseEnd_7007311 := by
    simpa [prefixWord, tailWord_7007311, baseEnd_7007311] using wordTrace_append hprefix tailTrace_7007311
  have hstable : (prefixWord ++ tailWord_7007311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007311).length < 2 ^ (prefixWord ++ tailWord_7007311).sum := by decide
  have hdescent : baseEnd_7007311 < baseStart_7007311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007331 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 7]
def baseStart_7007331 : Nat := 118140960795 + 7007331 * 2 ^ 59
def prefixEnd_7007331 : Nat := 4983230072969 + 3 ^ 40 * 7007331 * 2
def baseEnd_7007331 : Nat := 399792100905647613215153

theorem tailTrace_7007331 : CollatzResearch.WordTrace tailWord_7007331 prefixEnd_7007331 399792100905647613215153 := by
  unfold tailWord_7007331
  simp only [CollatzResearch.WordTrace]
  refine ⟨255578358176644018701229847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170385572117762679134153231 255578358176644018701229847)
  ·
    refine ⟨383367537264966028051844771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255578358176644018701229847 383367537264966028051844771)
    ·
      refine ⟨575051305897449042077767157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383367537264966028051844771 575051305897449042077767157)
      ·
        refine ⟨53911059927885847694790671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 575051305897449042077767157 53911059927885847694790671)
        ·
          refine ⟨80866589891828771542186007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53911059927885847694790671 80866589891828771542186007)
          ·
            refine ⟨121299884837743157313279011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80866589891828771542186007 121299884837743157313279011)
            ·
              refine ⟨181949827256614735969918517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121299884837743157313279011 181949827256614735969918517)
              ·
                refine ⟨17057796305307631497179861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181949827256614735969918517 17057796305307631497179861)
                ·
                  refine ⟨399792100905647613215153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17057796305307631497179861 399792100905647613215153)
                  ·
                    rfl

theorem cell23_7007331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 7].length) (baseStart_7007331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007331 prefixEnd_7007331 := by exact prefixLift 7007331
  have htrace : WordTrace (prefixWord ++ tailWord_7007331) baseStart_7007331 baseEnd_7007331 := by
    simpa [prefixWord, tailWord_7007331, baseEnd_7007331] using wordTrace_append hprefix tailTrace_7007331
  have hstable : (prefixWord ++ tailWord_7007331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007331).length < 2 ^ (prefixWord ++ tailWord_7007331).sum := by decide
  have hdescent : baseEnd_7007331 < baseStart_7007331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007338 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7007338 : Nat := 118140960795 + 7007338 * 2 ^ 59
def prefixEnd_7007338 : Nat := 4983230072969 + 3 ^ 40 * 7007338 * 2
def baseEnd_7007338 : Nat := 3598132502515409991548845

theorem tailTrace_7007338 : CollatzResearch.WordTrace tailWord_7007338 prefixEnd_7007338 3598132502515409991548845 := by
  unfold tailWord_7007338
  simp only [CollatzResearch.WordTrace]
  refine ⟨63894653371904664724183667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170385742325079105931156445 63894653371904664724183667)
  ·
    refine ⟨95841980057856997086275501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63894653371904664724183667 95841980057856997086275501)
    ·
      refine ⟨35940742521696373907353313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95841980057856997086275501 35940742521696373907353313)
      ·
        refine ⟨26955556891272280430514985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35940742521696373907353313 26955556891272280430514985)
        ·
          refine ⟨20216667668454210322886239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26955556891272280430514985 20216667668454210322886239)
          ·
            refine ⟨30325001502681315484329359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20216667668454210322886239 30325001502681315484329359)
            ·
              refine ⟨45487502254021973226494039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30325001502681315484329359 45487502254021973226494039)
              ·
                refine ⟨68231253381032959839741059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45487502254021973226494039 68231253381032959839741059)
                ·
                  refine ⟨102346880071549439759611589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68231253381032959839741059 102346880071549439759611589)
                  ·
                    refine ⟨19190040013415519954927173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102346880071549439759611589 19190040013415519954927173)
                    ·
                      refine ⟨3598132502515409991548845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19190040013415519954927173 3598132502515409991548845)
                      ·
                        rfl

theorem cell23_7007338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7007338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007338 prefixEnd_7007338 := by exact prefixLift 7007338
  have htrace : WordTrace (prefixWord ++ tailWord_7007338) baseStart_7007338 baseEnd_7007338 := by
    simpa [prefixWord, tailWord_7007338, baseEnd_7007338] using wordTrace_append hprefix tailTrace_7007338
  have hstable : (prefixWord ++ tailWord_7007338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007338).length < 2 ^ (prefixWord ++ tailWord_7007338).sum := by decide
  have hdescent : baseEnd_7007338 < baseStart_7007338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007342 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_7007342 : Nat := 118140960795 + 7007342 * 2 ^ 59
def prefixEnd_7007342 : Nat := 4983230072969 + 3 ^ 40 * 7007342 * 2
def baseEnd_7007342 : Nat := 3598134556438027975898827

theorem tailTrace_7007342 : CollatzResearch.WordTrace tailWord_7007342 prefixEnd_7007342 3598134556438027975898827 := by
  unfold tailWord_7007342
  simp only [CollatzResearch.WordTrace]
  refine ⟨31947344922450520947485035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170385839586402778386586853 31947344922450520947485035)
  ·
    refine ⟨47921017383675781421227553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31947344922450520947485035 47921017383675781421227553)
    ·
      refine ⟨35940763037756836065920665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47921017383675781421227553 35940763037756836065920665)
      ·
        refine ⟨26955572278317627049440499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35940763037756836065920665 26955572278317627049440499)
        ·
          refine ⟨40433358417476440574160749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26955572278317627049440499 40433358417476440574160749)
          ·
            refine ⟨15162509406553665215310281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40433358417476440574160749 15162509406553665215310281)
            ·
              refine ⟨11371882054915248911482711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15162509406553665215310281 11371882054915248911482711)
              ·
                refine ⟨17057823082372873367224067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11371882054915248911482711 17057823082372873367224067)
                ·
                  refine ⟨25586734623559310050836101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17057823082372873367224067 25586734623559310050836101)
                  ·
                    refine ⟨4797512741917370634531769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25586734623559310050836101 4797512741917370634531769)
                    ·
                      refine ⟨3598134556438027975898827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797512741917370634531769 3598134556438027975898827)
                      ·
                        rfl

theorem cell23_7007342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_7007342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007342 prefixEnd_7007342 := by exact prefixLift 7007342
  have htrace : WordTrace (prefixWord ++ tailWord_7007342) baseStart_7007342 baseEnd_7007342 := by
    simpa [prefixWord, tailWord_7007342, baseEnd_7007342] using wordTrace_append hprefix tailTrace_7007342
  have hstable : (prefixWord ++ tailWord_7007342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007342).length < 2 ^ (prefixWord ++ tailWord_7007342).sum := by decide
  have hdescent : baseEnd_7007342 < baseStart_7007342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007371 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 5]
def baseStart_7007371 : Nat := 118140960795 + 7007371 * 2 ^ 59
def prefixEnd_7007371 : Nat := 4983230072969 + 3 ^ 40 * 7007371 * 2
def baseEnd_7007371 : Nat := 3598149447377008362436193

theorem tailTrace_7007371 : CollatzResearch.WordTrace tailWord_7007371 prefixEnd_7007371 3598149447377008362436193 := by
  unfold tailWord_7007371
  simp only [CollatzResearch.WordTrace]
  refine ⟨255579817096499105532685967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170386544730999403688457311 255579817096499105532685967)
  ·
    refine ⟨383369725644748658299028951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255579817096499105532685967 383369725644748658299028951)
    ·
      refine ⟨575054588467122987448543427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383369725644748658299028951 575054588467122987448543427)
      ·
        refine ⟨862581882700684481172815141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575054588467122987448543427 862581882700684481172815141)
        ·
          refine ⟨161734103006378340219902839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 862581882700684481172815141 161734103006378340219902839)
          ·
            refine ⟨242601154509567510329854259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161734103006378340219902839 242601154509567510329854259)
            ·
              refine ⟨363901731764351265494781389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242601154509567510329854259 363901731764351265494781389)
              ·
                refine ⟨136463149411631724560543021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363901731764351265494781389 136463149411631724560543021)
                ·
                  refine ⟨51173681029361896710203633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136463149411631724560543021 51173681029361896710203633)
                  ·
                    refine ⟨38380260772021422532652725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51173681029361896710203633 38380260772021422532652725)
                    ·
                      refine ⟨3598149447377008362436193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38380260772021422532652725 3598149447377008362436193)
                      ·
                        rfl

theorem cell23_7007371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_7007371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007371 prefixEnd_7007371 := by exact prefixLift 7007371
  have htrace : WordTrace (prefixWord ++ tailWord_7007371) baseStart_7007371 baseEnd_7007371 := by
    simpa [prefixWord, tailWord_7007371, baseEnd_7007371] using wordTrace_append hprefix tailTrace_7007371
  have hstable : (prefixWord ++ tailWord_7007371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007371).length < 2 ^ (prefixWord ++ tailWord_7007371).sum := by decide
  have hdescent : baseEnd_7007371 < baseStart_7007371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007401 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_7007401 : Nat := 118140960795 + 7007401 * 2 ^ 59
def prefixEnd_7007401 : Nat := 4983230072969 + 3 ^ 40 * 7007401 * 2
def baseEnd_7007401 : Nat := 3598164851796643245061055

theorem tailTrace_7007401 : CollatzResearch.WordTrace tailWord_7007401 prefixEnd_7007401 3598164851796643245061055 := by
  unfold tailWord_7007401
  simp only [CollatzResearch.WordTrace]
  refine ⟨255580911286390420656278057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170387274190926947104185371 255580911286390420656278057)
  ·
    refine ⟨191685683464792815492208543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255580911286390420656278057 191685683464792815492208543)
    ·
      refine ⟨287528525197189223238312815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191685683464792815492208543 287528525197189223238312815)
      ·
        refine ⟨431292787795783834857469223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287528525197189223238312815 431292787795783834857469223)
        ·
          refine ⟨646939181693675752286203835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431292787795783834857469223 646939181693675752286203835)
          ·
            refine ⟨970408772540513628429305753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646939181693675752286203835 970408772540513628429305753)
            ·
              refine ⟨727806579405385221321979315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970408772540513628429305753 727806579405385221321979315)
              ·
                refine ⟨1091709869108077831982968973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727806579405385221321979315 1091709869108077831982968973)
                ·
                  refine ⟨409391200915529186993613365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091709869108077831982968973 409391200915529186993613365)
                  ·
                    refine ⟨38380425085830861280651253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 409391200915529186993613365 38380425085830861280651253)
                    ·
                      refine ⟨3598164851796643245061055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38380425085830861280651253 3598164851796643245061055)
                      ·
                        rfl

theorem cell23_7007401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_7007401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007401 prefixEnd_7007401 := by exact prefixLift 7007401
  have htrace : WordTrace (prefixWord ++ tailWord_7007401) baseStart_7007401 baseEnd_7007401 := by
    simpa [prefixWord, tailWord_7007401, baseEnd_7007401] using wordTrace_append hprefix tailTrace_7007401
  have hstable : (prefixWord ++ tailWord_7007401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007401).length < 2 ^ (prefixWord ++ tailWord_7007401).sum := by decide
  have hdescent : baseEnd_7007401 < baseStart_7007401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007455 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 6]
def baseStart_7007455 : Nat := 118140960795 + 7007455 * 2 ^ 59
def prefixEnd_7007455 : Nat := 4983230072969 + 3 ^ 40 * 7007455 * 2
def baseEnd_7007455 : Nat := 399799175527998448198423

theorem tailTrace_7007455 : CollatzResearch.WordTrace tailWord_7007455 prefixEnd_7007455 399799175527998448198423 := by
  unfold tailWord_7007455
  simp only [CollatzResearch.WordTrace]
  refine ⟨255582880828194787878743819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170388587218796525252495879 255582880828194787878743819)
  ·
    refine ⟨383374321242292181818115729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255582880828194787878743819 383374321242292181818115729)
    ·
      refine ⟨287530740931719136363586797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383374321242292181818115729 287530740931719136363586797)
      ·
        refine ⟨107824027849394676136345049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287530740931719136363586797 107824027849394676136345049)
        ·
          refine ⟨80868020887046007102258787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107824027849394676136345049 80868020887046007102258787)
          ·
            refine ⟨121302031330569010653388181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80868020887046007102258787 121302031330569010653388181)
            ·
              refine ⟨5686032718620422374377571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121302031330569010653388181 5686032718620422374377571)
              ·
                refine ⟨8529049077930633561566357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5686032718620422374377571 8529049077930633561566357)
                ·
                  refine ⟨399799175527998448198423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8529049077930633561566357 399799175527998448198423)
                  ·
                    rfl

theorem cell23_7007455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 6].length) (baseStart_7007455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007455 prefixEnd_7007455 := by exact prefixLift 7007455
  have htrace : WordTrace (prefixWord ++ tailWord_7007455) baseStart_7007455 baseEnd_7007455 := by
    simpa [prefixWord, tailWord_7007455, baseEnd_7007455] using wordTrace_append hprefix tailTrace_7007455
  have hstable : (prefixWord ++ tailWord_7007455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007455).length < 2 ^ (prefixWord ++ tailWord_7007455).sum := by decide
  have hdescent : baseEnd_7007455 < baseStart_7007455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007498 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_7007498 : Nat := 118140960795 + 7007498 * 2 ^ 59
def prefixEnd_7007498 : Nat := 4983230072969 + 3 ^ 40 * 7007498 * 2
def baseEnd_7007498 : Nat := 1199404886473376455182703

theorem tailTrace_7007498 : CollatzResearch.WordTrace tailWord_7007498 prefixEnd_7007498 1199404886473376455182703 := by
  unfold tailWord_7007498
  simp only [CollatzResearch.WordTrace]
  refine ⟨63896112291759751555639787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170389632778026004148372765 63896112291759751555639787)
  ·
    refine ⟨95844168437639627333459681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63896112291759751555639787 95844168437639627333459681)
    ·
      refine ⟨71883126328229720500094761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95844168437639627333459681 71883126328229720500094761)
      ·
        refine ⟨53912344746172290375071071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71883126328229720500094761 53912344746172290375071071)
        ·
          refine ⟨80868517119258435562606607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53912344746172290375071071 80868517119258435562606607)
          ·
            refine ⟨121302775678887653343909911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80868517119258435562606607 121302775678887653343909911)
            ·
              refine ⟨181954163518331480015864867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121302775678887653343909911 181954163518331480015864867)
              ·
                refine ⟨272931245277497220023797301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181954163518331480015864867 272931245277497220023797301)
                ·
                  refine ⟨25587304244765364377230997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272931245277497220023797301 25587304244765364377230997)
                  ·
                    refine ⟨1199404886473376455182703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25587304244765364377230997 1199404886473376455182703)
                    ·
                      rfl

theorem cell23_7007498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_7007498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007498 prefixEnd_7007498 := by exact prefixLift 7007498
  have htrace : WordTrace (prefixWord ++ tailWord_7007498) baseStart_7007498 baseEnd_7007498 := by
    simpa [prefixWord, tailWord_7007498, baseEnd_7007498] using wordTrace_append hprefix tailTrace_7007498
  have hstable : (prefixWord ++ tailWord_7007498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007498).length < 2 ^ (prefixWord ++ tailWord_7007498).sum := by decide
  have hdescent : baseEnd_7007498 < baseStart_7007498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007499 : List Nat := [1, 1, 1, 1, 5, 4, 1, 4, 1, 1, 3]
def baseStart_7007499 : Nat := 118140960795 + 7007499 * 2 ^ 59
def prefixEnd_7007499 : Nat := 4983230072969 + 3 ^ 40 * 7007499 * 2
def baseEnd_7007499 : Nat := 3598215172900783861635605

theorem tailTrace_7007499 : CollatzResearch.WordTrace tailWord_7007499 prefixEnd_7007499 3598215172900783861635605 := by
  unfold tailWord_7007499
  simp only [CollatzResearch.WordTrace]
  refine ⟨255584485640035383393345551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170389657093356922262230367 255584485640035383393345551)
  ·
    refine ⟨383376728460053075090018327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255584485640035383393345551 383376728460053075090018327)
    ·
      refine ⟨575065092690079612635027491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383376728460053075090018327 575065092690079612635027491)
      ·
        refine ⟨862597639035119418952541237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575065092690079612635027491 862597639035119418952541237)
        ·
          refine ⟨80868528659542445526800741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 862597639035119418952541237 80868528659542445526800741)
          ·
            refine ⟨15162849123664208536275139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80868528659542445526800741 15162849123664208536275139)
            ·
              refine ⟨22744273685496312804412709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15162849123664208536275139 22744273685496312804412709)
              ·
                refine ⟨4264551316030558650827383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22744273685496312804412709 4264551316030558650827383)
                ·
                  refine ⟨6396826974045837976241075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264551316030558650827383 6396826974045837976241075)
                  ·
                    refine ⟨9595240461068756964361613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6396826974045837976241075 9595240461068756964361613)
                    ·
                      refine ⟨3598215172900783861635605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9595240461068756964361613 3598215172900783861635605)
                      ·
                        rfl

theorem cell23_7007499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 1, 3].length) (baseStart_7007499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007499 prefixEnd_7007499 := by exact prefixLift 7007499
  have htrace : WordTrace (prefixWord ++ tailWord_7007499) baseStart_7007499 baseEnd_7007499 := by
    simpa [prefixWord, tailWord_7007499, baseEnd_7007499] using wordTrace_append hprefix tailTrace_7007499
  have hstable : (prefixWord ++ tailWord_7007499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007499).length < 2 ^ (prefixWord ++ tailWord_7007499).sum := by decide
  have hdescent : baseEnd_7007499 < baseStart_7007499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007533 : List Nat := [1, 5, 3, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7007533 : Nat := 118140960795 + 7007533 * 2 ^ 59
def prefixEnd_7007533 : Nat := 4983230072969 + 3 ^ 40 * 7007533 * 2
def baseEnd_7007533 : Nat := 3598232631243036728610449

theorem tailTrace_7007533 : CollatzResearch.WordTrace tailWord_7007533 prefixEnd_7007533 3598232631243036728610449 := by
  unfold tailWord_7007533
  simp only [CollatzResearch.WordTrace]
  refine ⟨255585725721912207200083253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170390483814608138133388835 255585725721912207200083253)
  ·
    refine ⟨23961161786429269425007805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255585725721912207200083253 23961161786429269425007805)
    ·
      refine ⟨8985435669910976034377927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23961161786429269425007805 8985435669910976034377927)
      ·
        refine ⟨13478153504866464051566891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8985435669910976034377927 13478153504866464051566891)
        ·
          refine ⟨20217230257299696077350337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13478153504866464051566891 20217230257299696077350337)
          ·
            refine ⟨15162922692974772058012753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20217230257299696077350337 15162922692974772058012753)
            ·
              refine ⟨11372192019731079043509565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15162922692974772058012753 11372192019731079043509565)
              ·
                refine ⟨4264572007399154641316087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11372192019731079043509565 4264572007399154641316087)
                ·
                  refine ⟨6396858011098731961974131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264572007399154641316087 6396858011098731961974131)
                  ·
                    refine ⟨9595287016648097942961197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6396858011098731961974131 9595287016648097942961197)
                    ·
                      refine ⟨3598232631243036728610449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9595287016648097942961197 3598232631243036728610449)
                      ·
                        rfl

theorem cell23_7007533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7007533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007533 prefixEnd_7007533 := by exact prefixLift 7007533
  have htrace : WordTrace (prefixWord ++ tailWord_7007533) baseStart_7007533 baseEnd_7007533 := by
    simpa [prefixWord, tailWord_7007533, baseEnd_7007533] using wordTrace_append hprefix tailTrace_7007533
  have hstable : (prefixWord ++ tailWord_7007533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007533).length < 2 ^ (prefixWord ++ tailWord_7007533).sum := by decide
  have hdescent : baseEnd_7007533 < baseStart_7007533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007539 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 1, 1, 4]
def baseStart_7007539 : Nat := 118140960795 + 7007539 * 2 ^ 59
def prefixEnd_7007539 : Nat := 4983230072969 + 3 ^ 40 * 7007539 * 2
def baseEnd_7007539 : Nat := 3598235712126963705135421

theorem tailTrace_7007539 : CollatzResearch.WordTrace tailWord_7007539 prefixEnd_7007539 3598235712126963705135421 := by
  unfold tailWord_7007539
  simp only [CollatzResearch.WordTrace]
  refine ⟨255585944559890470224801671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170390629706593646816534447 255585944559890470224801671)
  ·
    refine ⟨383378916839835705337202507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255585944559890470224801671 383378916839835705337202507)
    ·
      refine ⟨575068375259753558005803761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383378916839835705337202507 575068375259753558005803761)
      ·
        refine ⟨431301281444815168504352821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575068375259753558005803761 431301281444815168504352821)
        ·
          refine ⟨40434495135451422047283077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 431301281444815168504352821 40434495135451422047283077)
          ·
            refine ⟨7581467837897141633865577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40434495135451422047283077 7581467837897141633865577)
            ·
              refine ⟨5686100878422856225399183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7581467837897141633865577 5686100878422856225399183)
              ·
                refine ⟨8529151317634284338098775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5686100878422856225399183 8529151317634284338098775)
                ·
                  refine ⟨12793726976451426507148163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8529151317634284338098775 12793726976451426507148163)
                  ·
                    refine ⟨19190590464677139760722245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12793726976451426507148163 19190590464677139760722245)
                    ·
                      refine ⟨3598235712126963705135421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19190590464677139760722245 3598235712126963705135421)
                      ·
                        rfl

theorem cell23_7007539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 1, 4].length) (baseStart_7007539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007539 prefixEnd_7007539 := by exact prefixLift 7007539
  have htrace : WordTrace (prefixWord ++ tailWord_7007539) baseStart_7007539 baseEnd_7007539 := by
    simpa [prefixWord, tailWord_7007539, baseEnd_7007539] using wordTrace_append hprefix tailTrace_7007539
  have hstable : (prefixWord ++ tailWord_7007539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007539).length < 2 ^ (prefixWord ++ tailWord_7007539).sum := by decide
  have hdescent : baseEnd_7007539 < baseStart_7007539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007545 : List Nat := [1, 2, 1, 6, 2, 1, 10]
def baseStart_7007545 : Nat := 118140960795 + 7007545 * 2 ^ 59
def prefixEnd_7007545 : Nat := 4983230072969 + 3 ^ 40 * 7007545 * 2
def baseEnd_7007545 : Nat := 44422701148282601008153

theorem tailTrace_7007545 : CollatzResearch.WordTrace tailWord_7007545 prefixEnd_7007545 44422701148282601008153 := by
  unfold tailWord_7007545
  simp only [CollatzResearch.WordTrace]
  refine ⟨255586163397868733249520089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170390775598579155499680059 255586163397868733249520089)
  ·
    refine ⟨191689622548401549937140067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255586163397868733249520089 191689622548401549937140067)
    ·
      refine ⟨287534433822602324905710101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191689622548401549937140067 287534433822602324905710101)
      ·
        refine ⟨13478176585434483979955161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 287534433822602324905710101 13478176585434483979955161)
        ·
          refine ⟨10108632439075862984966371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13478176585434483979955161 10108632439075862984966371)
          ·
            refine ⟨15162948658613794477449557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10108632439075862984966371 15162948658613794477449557)
            ·
              refine ⟨44422701148282601008153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15162948658613794477449557 44422701148282601008153)
              ·
                rfl

theorem cell23_7007545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 10].length) (baseStart_7007545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007545 prefixEnd_7007545 := by exact prefixLift 7007545
  have htrace : WordTrace (prefixWord ++ tailWord_7007545) baseStart_7007545 baseEnd_7007545 := by
    simpa [prefixWord, tailWord_7007545, baseEnd_7007545] using wordTrace_append hprefix tailTrace_7007545
  have hstable : (prefixWord ++ tailWord_7007545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007545).length < 2 ^ (prefixWord ++ tailWord_7007545).sum := by decide
  have hdescent : baseEnd_7007545 < baseStart_7007545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007549 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_7007549 : Nat := 118140960795 + 7007549 * 2 ^ 59
def prefixEnd_7007549 : Nat := 4983230072969 + 3 ^ 40 * 7007549 * 2
def baseEnd_7007549 : Nat := 1199413615644502888670125

theorem tailTrace_7007549 : CollatzResearch.WordTrace tailWord_7007549 prefixEnd_7007549 1199413615644502888670125 := by
  unfold tailWord_7007549
  simp only [CollatzResearch.WordTrace]
  refine ⟨255586309289854241932665701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170390872859902827955110467 255586309289854241932665701)
  ·
    refine ⟨47922432991847670362374819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255586309289854241932665701 47922432991847670362374819)
    ·
      refine ⟨71883649487771505543562229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47922432991847670362374819 71883649487771505543562229)
      ·
        refine ⟨6739092139478578644708959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71883649487771505543562229 6739092139478578644708959)
        ·
          refine ⟨10108638209217867967063439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6739092139478578644708959 10108638209217867967063439)
          ·
            refine ⟨15162957313826801950595159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10108638209217867967063439 15162957313826801950595159)
            ·
              refine ⟨22744435970740202925892739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15162957313826801950595159 22744435970740202925892739)
              ·
                refine ⟨34116653956110304388839109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22744435970740202925892739 34116653956110304388839109)
                ·
                  refine ⟨6396872616770682072907333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34116653956110304388839109 6396872616770682072907333)
                  ·
                    refine ⟨1199413615644502888670125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6396872616770682072907333 1199413615644502888670125)
                    ·
                      rfl

theorem cell23_7007549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_7007549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007549 prefixEnd_7007549 := by exact prefixLift 7007549
  have htrace : WordTrace (prefixWord ++ tailWord_7007549) baseStart_7007549 baseEnd_7007549 := by
    simpa [prefixWord, tailWord_7007549, baseEnd_7007549] using wordTrace_append hprefix tailTrace_7007549
  have hstable : (prefixWord ++ tailWord_7007549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007549).length < 2 ^ (prefixWord ++ tailWord_7007549).sum := by decide
  have hdescent : baseEnd_7007549 < baseStart_7007549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007556 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_7007556 : Nat := 118140960795 + 7007556 * 2 ^ 59
def prefixEnd_7007556 : Nat := 4983230072969 + 3 ^ 40 * 7007556 * 2
def baseEnd_7007556 : Nat := 3598244441298090138622843

theorem tailTrace_7007556 : CollatzResearch.WordTrace tailWord_7007556 prefixEnd_7007556 3598244441298090138622843 := by
  unfold tailWord_7007556
  simp only [CollatzResearch.WordTrace]
  refine ⟨127793282300414441064085261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170391043067219254752113681 127793282300414441064085261)
  ·
    refine ⟨47922480862655415399031973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127793282300414441064085261 47922480862655415399031973)
    ·
      refine ⟨8985465161747890387318495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47922480862655415399031973 8985465161747890387318495)
      ·
        refine ⟨13478197742621835580977743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8985465161747890387318495 13478197742621835580977743)
        ·
          refine ⟨20217296613932753371466615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13478197742621835580977743 20217296613932753371466615)
          ·
            refine ⟨30325944920899130057199923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20217296613932753371466615 30325944920899130057199923)
            ·
              refine ⟨45488917381348695085799885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30325944920899130057199923 45488917381348695085799885)
              ·
                refine ⟨17058344018005760657174957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45488917381348695085799885 17058344018005760657174957)
                ·
                  refine ⟨6396879006752160246440609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17058344018005760657174957 6396879006752160246440609)
                  ·
                    refine ⟨4797659255064120184830457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6396879006752160246440609 4797659255064120184830457)
                    ·
                      refine ⟨3598244441298090138622843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797659255064120184830457 3598244441298090138622843)
                      ·
                        rfl

theorem cell23_7007556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_7007556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007556 prefixEnd_7007556 := by exact prefixLift 7007556
  have htrace : WordTrace (prefixWord ++ tailWord_7007556) baseStart_7007556 baseEnd_7007556 := by
    simpa [prefixWord, tailWord_7007556, baseEnd_7007556] using wordTrace_append hprefix tailTrace_7007556
  have hstable : (prefixWord ++ tailWord_7007556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007556).length < 2 ^ (prefixWord ++ tailWord_7007556).sum := by decide
  have hdescent : baseEnd_7007556 < baseStart_7007556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007652 : List Nat := [2, 3, 1, 2, 1, 1, 1, 7, 5]
def baseStart_7007652 : Nat := 118140960795 + 7007652 * 2 ^ 59
def prefixEnd_7007652 : Nat := 4983230072969 + 3 ^ 40 * 7007652 * 2
def baseEnd_7007652 : Nat := 399810415048991307002489

theorem tailTrace_7007652 : CollatzResearch.WordTrace tailWord_7007652 prefixEnd_7007652 399810415048991307002489 := by
  unfold tailWord_7007652
  simp only [CollatzResearch.WordTrace]
  refine ⟨127795033004240545261832605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170393377338987393682443473 127795033004240545261832605)
  ·
    refine ⟨47923137376590204473187227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127795033004240545261832605 47923137376590204473187227)
    ·
      refine ⟨71884706064885306709780841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47923137376590204473187227 71884706064885306709780841)
      ·
        refine ⟨53913529548663980032335631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71884706064885306709780841 53913529548663980032335631)
        ·
          refine ⟨80870294322995970048503447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53913529548663980032335631 80870294322995970048503447)
          ·
            refine ⟨121305441484493955072755171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80870294322995970048503447 121305441484493955072755171)
            ·
              refine ⟨181958162226740932609132757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121305441484493955072755171 181958162226740932609132757)
              ·
                refine ⟨4264644427189240608026549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 181958162226740932609132757 4264644427189240608026549)
                ·
                  refine ⟨399810415048991307002489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4264644427189240608026549 399810415048991307002489)
                  ·
                    rfl

theorem cell23_7007652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_7007652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007652 prefixEnd_7007652 := by exact prefixLift 7007652
  have htrace : WordTrace (prefixWord ++ tailWord_7007652) baseStart_7007652 baseEnd_7007652 := by
    simpa [prefixWord, tailWord_7007652, baseEnd_7007652] using wordTrace_append hprefix tailTrace_7007652
  have hstable : (prefixWord ++ tailWord_7007652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007652).length < 2 ^ (prefixWord ++ tailWord_7007652).sum := by decide
  have hdescent : baseEnd_7007652 < baseStart_7007652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007669 : List Nat := [1, 3, 3, 2, 2, 2, 1, 4, 5]
def baseStart_7007669 : Nat := 118140960795 + 7007669 * 2 ^ 59
def prefixEnd_7007669 : Nat := 4983230072969 + 3 ^ 40 * 7007669 * 2
def baseEnd_7007669 : Nat := 399811384956894244056647

theorem tailTrace_7007669 : CollatzResearch.WordTrace tailWord_7007669 prefixEnd_7007669 399811384956894244056647 := by
  unfold tailWord_7007669
  simp only [CollatzResearch.WordTrace]
  refine ⟨255590686049419502427034061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170393790699613001618022707 255590686049419502427034061)
  ·
    refine ⟨95846507268532313410137773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255590686049419502427034061 95846507268532313410137773)
    ·
      refine ⟨35942440225699617528801665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95846507268532313410137773 35942440225699617528801665)
      ·
        refine ⟨26956830169274713146601249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35942440225699617528801665 26956830169274713146601249)
        ·
          refine ⟨20217622626956034859950937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26956830169274713146601249 20217622626956034859950937)
          ·
            refine ⟨15163216970217026144963203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20217622626956034859950937 15163216970217026144963203)
            ·
              refine ⟨22744825455325539217444805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15163216970217026144963203 22744825455325539217444805)
              ·
                refine ⟨4264654772873538603270901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22744825455325539217444805 4264654772873538603270901)
                ·
                  refine ⟨399811384956894244056647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4264654772873538603270901 399811384956894244056647)
                  ·
                    rfl

theorem cell23_7007669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_7007669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007669 prefixEnd_7007669 := by exact prefixLift 7007669
  have htrace : WordTrace (prefixWord ++ tailWord_7007669) baseStart_7007669 baseEnd_7007669 := by
    simpa [prefixWord, tailWord_7007669, baseEnd_7007669] using wordTrace_append hprefix tailTrace_7007669
  have hstable : (prefixWord ++ tailWord_7007669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007669).length < 2 ^ (prefixWord ++ tailWord_7007669).sum := by decide
  have hdescent : baseEnd_7007669 < baseStart_7007669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007672 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 2, 5, 2]
def baseStart_7007672 : Nat := 118140960795 + 7007672 * 2 ^ 59
def prefixEnd_7007672 : Nat := 4983230072969 + 3 ^ 40 * 7007672 * 2
def baseEnd_7007672 : Nat := 3598304005054011684772309

theorem tailTrace_7007672 : CollatzResearch.WordTrace tailWord_7007672 prefixEnd_7007672 3598304005054011684772309 := by
  unfold tailWord_7007672
  simp only [CollatzResearch.WordTrace]
  refine ⟨127795397734204316969696635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170393863645605755959595513 127795397734204316969696635)
  ·
    refine ⟨191693096601306475454544953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127795397734204316969696635 191693096601306475454544953)
    ·
      refine ⟨143769822450979856590908715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191693096601306475454544953 143769822450979856590908715)
      ·
        refine ⟨215654733676469784886363073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143769822450979856590908715 215654733676469784886363073)
        ·
          refine ⟨161741050257352338664772305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215654733676469784886363073 161741050257352338664772305)
          ·
            refine ⟨121305787693014253998579229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161741050257352338664772305 121305787693014253998579229)
            ·
              refine ⟨45489670384880345249467211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121305787693014253998579229 45489670384880345249467211)
              ·
                refine ⟨68234505577320517874200817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45489670384880345249467211 68234505577320517874200817)
                ·
                  refine ⟨51175879182990388405650613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68234505577320517874200817 51175879182990388405650613)
                  ·
                    refine ⟨4797738673405348913029745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51175879182990388405650613 4797738673405348913029745)
                    ·
                      refine ⟨3598304005054011684772309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797738673405348913029745 3598304005054011684772309)
                      ·
                        rfl

theorem cell23_7007672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_7007672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007672 prefixEnd_7007672 := by exact prefixLift 7007672
  have htrace : WordTrace (prefixWord ++ tailWord_7007672) baseStart_7007672 baseEnd_7007672 := by
    simpa [prefixWord, tailWord_7007672, baseEnd_7007672] using wordTrace_append hprefix tailTrace_7007672
  have hstable : (prefixWord ++ tailWord_7007672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007672).length < 2 ^ (prefixWord ++ tailWord_7007672).sum := by decide
  have hdescent : baseEnd_7007672 < baseStart_7007672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007719 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_7007719 : Nat := 118140960795 + 7007719 * 2 ^ 59
def prefixEnd_7007719 : Nat := 4983230072969 + 3 ^ 40 * 7007719 * 2
def baseEnd_7007719 : Nat := 3598328138644773000884593

theorem tailTrace_7007719 : CollatzResearch.WordTrace tailWord_7007719 prefixEnd_7007719 3598328138644773000884593 := by
  unfold tailWord_7007719
  simp only [CollatzResearch.WordTrace]
  refine ⟨255592509699238360966354211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170395006466158907310902807 255592509699238360966354211)
  ·
    refine ⟨383388764548857541449531317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255592509699238360966354211 383388764548857541449531317)
    ·
      refine ⟨35942696676455394510893561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 383388764548857541449531317 35942696676455394510893561)
      ·
        refine ⟨26957022507341545883170171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35942696676455394510893561 26957022507341545883170171)
        ·
          refine ⟨40435533761012318824755257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26957022507341545883170171 40435533761012318824755257)
          ·
            refine ⟨30326650320759239118566443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40435533761012318824755257 30326650320759239118566443)
            ·
              refine ⟨45489975481138858677849665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30326650320759239118566443 45489975481138858677849665)
              ·
                refine ⟨34117481610854144008387249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45489975481138858677849665 34117481610854144008387249)
                ·
                  refine ⟨25588111208140608006290437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34117481610854144008387249 25588111208140608006290437)
                  ·
                    refine ⟨4797770851526364001179457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25588111208140608006290437 4797770851526364001179457)
                    ·
                      refine ⟨3598328138644773000884593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797770851526364001179457 3598328138644773000884593)
                      ·
                        rfl

theorem cell23_7007719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_7007719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007719 prefixEnd_7007719 := by exact prefixLift 7007719
  have htrace : WordTrace (prefixWord ++ tailWord_7007719) baseStart_7007719 baseEnd_7007719 := by
    simpa [prefixWord, tailWord_7007719, baseEnd_7007719] using wordTrace_append hprefix tailTrace_7007719
  have hstable : (prefixWord ++ tailWord_7007719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007719).length < 2 ^ (prefixWord ++ tailWord_7007719).sum := by decide
  have hdescent : baseEnd_7007719 < baseStart_7007719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007729 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 3, 4]
def baseStart_7007729 : Nat := 118140960795 + 7007729 * 2 ^ 59
def prefixEnd_7007729 : Nat := 4983230072969 + 3 ^ 40 * 7007729 * 2
def baseEnd_7007729 : Nat := 1199444424483772653919849

theorem tailTrace_7007729 : CollatzResearch.WordTrace tailWord_7007729 prefixEnd_7007729 1199444424483772653919849 := by
  unfold tailWord_7007729
  simp only [CollatzResearch.WordTrace]
  refine ⟨255592874429202132674218241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170395249619468088449478827 255592874429202132674218241)
  ·
    refine ⟨191694655821901599505663681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255592874429202132674218241 191694655821901599505663681)
    ·
      refine ⟨143770991866426199629247761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191694655821901599505663681 143770991866426199629247761)
      ·
        refine ⟨107828243899819649721935821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143770991866426199629247761 107828243899819649721935821)
        ·
          refine ⟨40435591462432368645725933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107828243899819649721935821 40435591462432368645725933)
          ·
            refine ⟨15163346798412138242147225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40435591462432368645725933 15163346798412138242147225)
            ·
              refine ⟨11372510098809103681610419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15163346798412138242147225 11372510098809103681610419)
              ·
                refine ⟨17058765148213655522415629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11372510098809103681610419 17058765148213655522415629)
                ·
                  refine ⟨6397036930580120820905861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17058765148213655522415629 6397036930580120820905861)
                  ·
                    refine ⟨1199444424483772653919849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6397036930580120820905861 1199444424483772653919849)
                    ·
                      rfl

theorem cell23_7007729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_7007729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007729 prefixEnd_7007729 := by exact prefixLift 7007729
  have htrace : WordTrace (prefixWord ++ tailWord_7007729) baseStart_7007729 baseEnd_7007729 := by
    simpa [prefixWord, tailWord_7007729, baseEnd_7007729] using wordTrace_append hprefix tailTrace_7007729
  have hstable : (prefixWord ++ tailWord_7007729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007729).length < 2 ^ (prefixWord ++ tailWord_7007729).sum := by decide
  have hdescent : baseEnd_7007729 < baseStart_7007729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007746 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7007746 : Nat := 118140960795 + 7007746 * 2 ^ 59
def prefixEnd_7007746 : Nat := 4983230072969 + 3 ^ 40 * 7007746 * 2
def baseEnd_7007746 : Nat := 1199447334207481465082323

theorem tailTrace_7007746 : CollatzResearch.WordTrace tailWord_7007746 prefixEnd_7007746 1199447334207481465082323 := by
  unfold tailWord_7007746
  simp only [CollatzResearch.WordTrace]
  refine ⟨63898373617535136144396773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170395662980093696385058061 63898373617535136144396773)
  ·
    refine ⟨11980945053287838027074395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63898373617535136144396773 11980945053287838027074395)
    ·
      refine ⟨17971417579931757040611593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11980945053287838027074395 17971417579931757040611593)
      ·
        refine ⟨13478563184948817780458695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17971417579931757040611593 13478563184948817780458695)
        ·
          refine ⟨20217844777423226670688043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13478563184948817780458695 20217844777423226670688043)
          ·
            refine ⟨30326767166134840006032065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20217844777423226670688043 30326767166134840006032065)
            ·
              refine ⟨22745075374601130004524049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30326767166134840006032065 22745075374601130004524049)
              ·
                refine ⟨17058806530950847503393037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22745075374601130004524049 17058806530950847503393037)
                ·
                  refine ⟨6397052449106567813772389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17058806530950847503393037 6397052449106567813772389)
                  ·
                    refine ⟨1199447334207481465082323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6397052449106567813772389 1199447334207481465082323)
                    ·
                      rfl

theorem cell23_7007746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7007746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007746 prefixEnd_7007746 := by exact prefixLift 7007746
  have htrace : WordTrace (prefixWord ++ tailWord_7007746) baseStart_7007746 baseEnd_7007746 := by
    simpa [prefixWord, tailWord_7007746, baseEnd_7007746] using wordTrace_append hprefix tailTrace_7007746
  have hstable : (prefixWord ++ tailWord_7007746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007746).length < 2 ^ (prefixWord ++ tailWord_7007746).sum := by decide
  have hdescent : baseEnd_7007746 < baseStart_7007746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007792 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_7007792 : Nat := 118140960795 + 7007792 * 2 ^ 59
def prefixEnd_7007792 : Nat := 4983230072969 + 3 ^ 40 * 7007792 * 2
def baseEnd_7007792 : Nat := 3598365622732551215271757

theorem tailTrace_7007792 : CollatzResearch.WordTrace tailWord_7007792 prefixEnd_7007792 3598365622732551215271757 := by
  unfold tailWord_7007792
  simp only [CollatzResearch.WordTrace]
  refine ⟨127797586113986947216880815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170396781485315929622507753 127797586113986947216880815)
  ·
    refine ⟨191696379170980420825321223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127797586113986947216880815 191696379170980420825321223)
    ·
      refine ⟨287544568756470631237981835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191696379170980420825321223 287544568756470631237981835)
      ·
        refine ⟨431316853134705946856972753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287544568756470631237981835 431316853134705946856972753)
        ·
          refine ⟨323487639851029460142729565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431316853134705946856972753 323487639851029460142729565)
          ·
            refine ⟨121307864944136047553523587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323487639851029460142729565 121307864944136047553523587)
            ·
              refine ⟨181961797416204071330285381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121307864944136047553523587 181961797416204071330285381)
              ·
                refine ⟨34117837015538263374428509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181961797416204071330285381 34117837015538263374428509)
                ·
                  refine ⟨12794188880826848765410691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34117837015538263374428509 12794188880826848765410691)
                  ·
                    refine ⟨19191283321240273148116037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12794188880826848765410691 19191283321240273148116037)
                    ·
                      refine ⟨3598365622732551215271757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19191283321240273148116037 3598365622732551215271757)
                      ·
                        rfl

theorem cell23_7007792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_7007792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007792 prefixEnd_7007792 := by exact prefixLift 7007792
  have htrace : WordTrace (prefixWord ++ tailWord_7007792) baseStart_7007792 baseEnd_7007792 := by
    simpa [prefixWord, tailWord_7007792, baseEnd_7007792] using wordTrace_append hprefix tailTrace_7007792
  have hstable : (prefixWord ++ tailWord_7007792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007792).length < 2 ^ (prefixWord ++ tailWord_7007792).sum := by decide
  have hdescent : baseEnd_7007792 < baseStart_7007792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007802 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_7007802 : Nat := 118140960795 + 7007802 * 2 ^ 59
def prefixEnd_7007802 : Nat := 4983230072969 + 3 ^ 40 * 7007802 * 2
def baseEnd_7007802 : Nat := 1199456919179698725382237

theorem tailTrace_7007802 : CollatzResearch.WordTrace tailWord_7007802 prefixEnd_7007802 1199456919179698725382237 := by
  unfold tailWord_7007802
  simp only [CollatzResearch.WordTrace]
  refine ⟨63898884239484416535406415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170397024638625110761083773 63898884239484416535406415)
  ·
    refine ⟨95848326359226624803109623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63898884239484416535406415 95848326359226624803109623)
    ·
      refine ⟨143772489538839937204664435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95848326359226624803109623 143772489538839937204664435)
      ·
        refine ⟨215658734308259905806996653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143772489538839937204664435 215658734308259905806996653)
        ·
          refine ⟨80872025365597464677623745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215658734308259905806996653 80872025365597464677623745)
          ·
            refine ⟨60654019024198098508217809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80872025365597464677623745 60654019024198098508217809)
            ·
              refine ⟨45490514268148573881163357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60654019024198098508217809 45490514268148573881163357)
              ·
                refine ⟨17058942850555715205436259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45490514268148573881163357 17058942850555715205436259)
                ·
                  refine ⟨25588414275833572808154389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17058942850555715205436259 25588414275833572808154389)
                  ·
                    refine ⟨1199456919179698725382237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25588414275833572808154389 1199456919179698725382237)
                    ·
                      rfl

theorem cell23_7007802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_7007802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007802 prefixEnd_7007802 := by exact prefixLift 7007802
  have htrace : WordTrace (prefixWord ++ tailWord_7007802) baseStart_7007802 baseEnd_7007802 := by
    simpa [prefixWord, tailWord_7007802, baseEnd_7007802] using wordTrace_append hprefix tailTrace_7007802
  have hstable : (prefixWord ++ tailWord_7007802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007802).length < 2 ^ (prefixWord ++ tailWord_7007802).sum := by decide
  have hdescent : baseEnd_7007802 < baseStart_7007802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007809 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_7007809 : Nat := 118140960795 + 7007809 * 2 ^ 59
def prefixEnd_7007809 : Nat := 4983230072969 + 3 ^ 40 * 7007809 * 2
def baseEnd_7007809 : Nat := 3598374351903677648759179

theorem tailTrace_7007809 : CollatzResearch.WordTrace tailWord_7007809 prefixEnd_7007809 3598374351903677648759179 := by
  unfold tailWord_7007809
  simp only [CollatzResearch.WordTrace]
  refine ⟨255595792268912306337130481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170397194845941537558086987 255595792268912306337130481)
  ·
    refine ⟨191696844201684229752847861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255595792268912306337130481 191696844201684229752847861)
    ·
      refine ⟨17971579143907896539329487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191696844201684229752847861 17971579143907896539329487)
      ·
        refine ⟨26957368715861844808994231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17971579143907896539329487 26957368715861844808994231)
        ·
          refine ⟨40436053073792767213491347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26957368715861844808994231 40436053073792767213491347)
          ·
            refine ⟨60654079610689150820237021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40436053073792767213491347 60654079610689150820237021)
            ·
              refine ⟨22745279854008431557588883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60654079610689150820237021 22745279854008431557588883)
              ·
                refine ⟨34117919781012647336383325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22745279854008431557588883 34117919781012647336383325)
                ·
                  refine ⟨12794219917879742751143747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34117919781012647336383325 12794219917879742751143747)
                  ·
                    refine ⟨19191329876819614126715621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12794219917879742751143747 19191329876819614126715621)
                    ·
                      refine ⟨3598374351903677648759179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19191329876819614126715621 3598374351903677648759179)
                      ·
                        rfl

theorem cell23_7007809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_7007809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007809 prefixEnd_7007809 := by exact prefixLift 7007809
  have htrace : WordTrace (prefixWord ++ tailWord_7007809) baseStart_7007809 baseEnd_7007809 := by
    simpa [prefixWord, tailWord_7007809, baseEnd_7007809] using wordTrace_append hprefix tailTrace_7007809
  have hstable : (prefixWord ++ tailWord_7007809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007809).length < 2 ^ (prefixWord ++ tailWord_7007809).sum := by decide
  have hdescent : baseEnd_7007809 < baseStart_7007809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007836 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_7007836 : Nat := 118140960795 + 7007836 * 2 ^ 59
def prefixEnd_7007836 : Nat := 4983230072969 + 3 ^ 40 * 7007836 * 2
def baseEnd_7007836 : Nat := 1199462738627116347707185

theorem tailTrace_7007836 : CollatzResearch.WordTrace tailWord_7007836 prefixEnd_7007836 1199462738627116347707185 := by
  unfold tailWord_7007836
  simp only [CollatzResearch.WordTrace]
  refine ⟨127798388519907244974181681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170397851359876326632242241 127798388519907244974181681)
  ·
    refine ⟨95848791389930433730636261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127798388519907244974181681 95848791389930433730636261)
    ·
      refine ⟨17971648385611956324494299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95848791389930433730636261 17971648385611956324494299)
      ·
        refine ⟨26957472578417934486741449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17971648385611956324494299 26957472578417934486741449)
        ·
          refine ⟨20218104433813450865056087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26957472578417934486741449 20218104433813450865056087)
          ·
            refine ⟨30327156650720176297584131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20218104433813450865056087 30327156650720176297584131)
            ·
              refine ⟨45490734976080264446376197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30327156650720176297584131 45490734976080264446376197)
              ·
                refine ⟨8529512808015049583695537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45490734976080264446376197 8529512808015049583695537)
                ·
                  refine ⟨6397134606011287187771653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8529512808015049583695537 6397134606011287187771653)
                  ·
                    refine ⟨1199462738627116347707185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6397134606011287187771653 1199462738627116347707185)
                    ·
                      rfl

theorem cell23_7007836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_7007836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007836 prefixEnd_7007836 := by exact prefixLift 7007836
  have htrace : WordTrace (prefixWord ++ tailWord_7007836) baseStart_7007836 baseEnd_7007836 := by
    simpa [prefixWord, tailWord_7007836, baseEnd_7007836] using wordTrace_append hprefix tailTrace_7007836
  have hstable : (prefixWord ++ tailWord_7007836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007836).length < 2 ^ (prefixWord ++ tailWord_7007836).sum := by decide
  have hdescent : baseEnd_7007836 < baseStart_7007836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007837 : List Nat := [1, 4, 4, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7007837 : Nat := 118140960795 + 7007837 * 2 ^ 59
def prefixEnd_7007837 : Nat := 4983230072969 + 3 ^ 40 * 7007837 * 2
def baseEnd_7007837 : Nat := 3598388729362003539209051

theorem tailTrace_7007837 : CollatzResearch.WordTrace tailWord_7007837 prefixEnd_7007837 3598388729362003539209051 := by
  unfold tailWord_7007837
  simp only [CollatzResearch.WordTrace]
  refine ⟨255596813512810867119149765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170397875675207244746099843 255596813512810867119149765)
  ·
    refine ⟨47924402533652037584840581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255596813512810867119149765 47924402533652037584840581)
    ·
      refine ⟨8985825475059757047157609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47924402533652037584840581 8985825475059757047157609)
      ·
        refine ⟨6739369106294817785368207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8985825475059757047157609 6739369106294817785368207)
        ·
          refine ⟨10109053659442226678052311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6739369106294817785368207 10109053659442226678052311)
          ·
            refine ⟨15163580489163340017078467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10109053659442226678052311 15163580489163340017078467)
            ·
              refine ⟨22745370733745010025617701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15163580489163340017078467 22745370733745010025617701)
              ·
                refine ⟨4264757012577189379803319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22745370733745010025617701 4264757012577189379803319)
                ·
                  refine ⟨6397135518865784069704979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264757012577189379803319 6397135518865784069704979)
                  ·
                    refine ⟨9595703278298676104557469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6397135518865784069704979 9595703278298676104557469)
                    ·
                      refine ⟨3598388729362003539209051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9595703278298676104557469 3598388729362003539209051)
                      ·
                        rfl

theorem cell23_7007837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7007837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007837 prefixEnd_7007837 := by exact prefixLift 7007837
  have htrace : WordTrace (prefixWord ++ tailWord_7007837) baseStart_7007837 baseEnd_7007837 := by
    simpa [prefixWord, tailWord_7007837, baseEnd_7007837] using wordTrace_append hprefix tailTrace_7007837
  have hstable : (prefixWord ++ tailWord_7007837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007837).length < 2 ^ (prefixWord ++ tailWord_7007837).sum := by decide
  have hdescent : baseEnd_7007837 < baseStart_7007837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007872 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_7007872 : Nat := 118140960795 + 7007872 * 2 ^ 59
def prefixEnd_7007872 : Nat := 4983230072969 + 3 ^ 40 * 7007872 * 2
def baseEnd_7007872 : Nat := 3598406701184910902271389

theorem tailTrace_7007872 : CollatzResearch.WordTrace tailWord_7007872 prefixEnd_7007872 3598406701184910902271389 := by
  unfold tailWord_7007872
  simp only [CollatzResearch.WordTrace]
  refine ⟨127799045033842034048336935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170398726711789378731115913 127799045033842034048336935)
  ·
    refine ⟨191698567550763051072505403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127799045033842034048336935 191698567550763051072505403)
    ·
      refine ⟨287547851326144576608758105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191698567550763051072505403 287547851326144576608758105)
      ·
        refine ⟨215660888494608432456568579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287547851326144576608758105 215660888494608432456568579)
        ·
          refine ⟨323491332741912648684852869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215660888494608432456568579 323491332741912648684852869)
          ·
            refine ⟨60654624889108621628409913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323491332741912648684852869 60654624889108621628409913)
            ·
              refine ⟨45490968666831466221307435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60654624889108621628409913 45490968666831466221307435)
              ·
                refine ⟨68236453000247199331961153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45490968666831466221307435 68236453000247199331961153)
                ·
                  refine ⟨51177339750185399498970865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68236453000247199331961153 51177339750185399498970865)
                  ·
                    refine ⟨38383004812639049624228149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51177339750185399498970865 38383004812639049624228149)
                    ·
                      refine ⟨3598406701184910902271389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38383004812639049624228149 3598406701184910902271389)
                      ·
                        rfl

theorem cell23_7007872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_7007872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007872 prefixEnd_7007872 := by exact prefixLift 7007872
  have htrace : WordTrace (prefixWord ++ tailWord_7007872) baseStart_7007872 baseEnd_7007872 := by
    simpa [prefixWord, tailWord_7007872, baseEnd_7007872] using wordTrace_append hprefix tailTrace_7007872
  have hstable : (prefixWord ++ tailWord_7007872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007872).length < 2 ^ (prefixWord ++ tailWord_7007872).sum := by decide
  have hdescent : baseEnd_7007872 < baseStart_7007872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007952 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 3, 7]
def baseStart_7007952 : Nat := 118140960795 + 7007952 * 2 ^ 59
def prefixEnd_7007952 : Nat := 4983230072969 + 3 ^ 40 * 7007952 * 2
def baseEnd_7007952 : Nat := 1199482593212423529757007

theorem tailTrace_7007952 : CollatzResearch.WordTrace tailWord_7007952 prefixEnd_7007952 1199482593212423529757007 := by
  unfold tailWord_7007952
  simp only [CollatzResearch.WordTrace]
  refine ⟨127800503953697120879793055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170400671938262827839724073 127800503953697120879793055)
  ·
    refine ⟨191700755930545681319689583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127800503953697120879793055 191700755930545681319689583)
    ·
      refine ⟨287551133895818521979534375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191700755930545681319689583 287551133895818521979534375)
      ·
        refine ⟨431326700843727782969301563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287551133895818521979534375 431326700843727782969301563)
        ·
          refine ⟨646990051265591674453952345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431326700843727782969301563 646990051265591674453952345)
          ·
            refine ⟨485242538449193755840464259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646990051265591674453952345 485242538449193755840464259)
            ·
              refine ⟨727863807673790633760696389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485242538449193755840464259 727863807673790633760696389)
              ·
                refine ⟨136474463938835743830130573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 727863807673790633760696389 136474463938835743830130573)
                ·
                  refine ⟨51177923977063403936298965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136474463938835743830130573 51177923977063403936298965)
                  ·
                    refine ⟨1199482593212423529757007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51177923977063403936298965 1199482593212423529757007)
                    ·
                      rfl

theorem cell23_7007952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_7007952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007952 prefixEnd_7007952 := by exact prefixLift 7007952
  have htrace : WordTrace (prefixWord ++ tailWord_7007952) baseStart_7007952 baseEnd_7007952 := by
    simpa [prefixWord, tailWord_7007952, baseEnd_7007952] using wordTrace_append hprefix tailTrace_7007952
  have hstable : (prefixWord ++ tailWord_7007952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007952).length < 2 ^ (prefixWord ++ tailWord_7007952).sum := by decide
  have hdescent : baseEnd_7007952 < baseStart_7007952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007956 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 7]
def baseStart_7007956 : Nat := 118140960795 + 7007956 * 2 ^ 59
def prefixEnd_7007956 : Nat := 4983230072969 + 3 ^ 40 * 7007956 * 2
def baseEnd_7007956 : Nat := 399827759284432063735667

theorem tailTrace_7007956 : CollatzResearch.WordTrace tailWord_7007956 prefixEnd_7007956 399827759284432063735667 := by
  unfold tailWord_7007956
  simp only [CollatzResearch.WordTrace]
  refine ⟨127800576899689875221365861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170400769199586500295154481 127800576899689875221365861)
  ·
    refine ⟨23962608168691851604006099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127800576899689875221365861 23962608168691851604006099)
    ·
      refine ⟨35943912253037777406009149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23962608168691851604006099 35943912253037777406009149)
      ·
        refine ⟨13478967094889166527253431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35943912253037777406009149 13478967094889166527253431)
        ·
          refine ⟨20218450642333749790880147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13478967094889166527253431 20218450642333749790880147)
          ·
            refine ⟨30327675963500624686320221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20218450642333749790880147 30327675963500624686320221)
            ·
              refine ⟨11372878486312734257370083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30327675963500624686320221 11372878486312734257370083)
              ·
                refine ⟨17059317729469101386055125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11372878486312734257370083 17059317729469101386055125)
                ·
                  refine ⟨399827759284432063735667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17059317729469101386055125 399827759284432063735667)
                  ·
                    rfl

theorem cell23_7007956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_7007956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007956 prefixEnd_7007956 := by exact prefixLift 7007956
  have htrace : WordTrace (prefixWord ++ tailWord_7007956) baseStart_7007956 baseEnd_7007956 := by
    simpa [prefixWord, tailWord_7007956, baseEnd_7007956] using wordTrace_append hprefix tailTrace_7007956
  have hstable : (prefixWord ++ tailWord_7007956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007956).length < 2 ^ (prefixWord ++ tailWord_7007956).sum := by decide
  have hdescent : baseEnd_7007956 < baseStart_7007956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7007986 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_7007986 : Nat := 118140960795 + 7007986 * 2 ^ 59
def prefixEnd_7007986 : Nat := 4983230072969 + 3 ^ 40 * 7007986 * 2
def baseEnd_7007986 : Nat := 1199488412659841152081955

theorem tailTrace_7007986 : CollatzResearch.WordTrace tailWord_7007986 prefixEnd_7007986 1199488412659841152081955 := by
  unfold tailWord_7007986
  simp only [CollatzResearch.WordTrace]
  refine ⟨63900561997317766391580953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170401498659514043710882541 63900561997317766391580953)
  ·
    refine ⟨47925421497988324793685715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63900561997317766391580953 47925421497988324793685715)
    ·
      refine ⟨71888132246982487190528573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47925421497988324793685715 71888132246982487190528573)
      ·
        refine ⟨26958049592618432696448215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71888132246982487190528573 26958049592618432696448215)
        ·
          refine ⟨40437074388927649044672323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26958049592618432696448215 40437074388927649044672323)
          ·
            refine ⟨60655611583391473567008485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40437074388927649044672323 60655611583391473567008485)
            ·
              refine ⟨11372927171885901293814091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60655611583391473567008485 11372927171885901293814091)
              ·
                refine ⟨17059390757828851940721137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11372927171885901293814091 17059390757828851940721137)
                ·
                  refine ⟨12794543068371638955540853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17059390757828851940721137 12794543068371638955540853)
                  ·
                    refine ⟨1199488412659841152081955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12794543068371638955540853 1199488412659841152081955)
                    ·
                      rfl

theorem cell23_7007986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_7007986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7007986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7007986 prefixEnd_7007986 := by exact prefixLift 7007986
  have htrace : WordTrace (prefixWord ++ tailWord_7007986) baseStart_7007986 baseEnd_7007986 := by
    simpa [prefixWord, tailWord_7007986, baseEnd_7007986] using wordTrace_append hprefix tailTrace_7007986
  have hstable : (prefixWord ++ tailWord_7007986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7007986).length < 2 ^ (prefixWord ++ tailWord_7007986).sum := by decide
  have hdescent : baseEnd_7007986 < baseStart_7007986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7007986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008007 : List Nat := [1, 1, 4, 4, 3, 1, 2, 2, 5]
def baseStart_7008007 : Nat := 118140960795 + 7008007 * 2 ^ 59
def prefixEnd_7008007 : Nat := 4983230072969 + 3 ^ 40 * 7008007 * 2
def baseEnd_7008007 : Nat := 399830669008140874898141

theorem tailTrace_7008007 : CollatzResearch.WordTrace tailWord_7008007 prefixEnd_7008007 399830669008140874898141 := by
  unfold tailWord_7008007
  simp only [CollatzResearch.WordTrace]
  refine ⟨255603013922194986152838275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170402009281463324101892183 255603013922194986152838275)
  ·
    refine ⟨383404520883292479229257413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255603013922194986152838275 383404520883292479229257413)
    ·
      refine ⟨71888347665617339855485765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383404520883292479229257413 71888347665617339855485765)
      ·
        refine ⟨13479065187303251222903581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71888347665617339855485765 13479065187303251222903581)
        ·
          refine ⟨5054649445238719208588843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13479065187303251222903581 5054649445238719208588843)
          ·
            refine ⟨7581974167858078812883265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054649445238719208588843 7581974167858078812883265)
            ·
              refine ⟨5686480625893559109662449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7581974167858078812883265 5686480625893559109662449)
              ·
                refine ⟨4264860469420169332246837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5686480625893559109662449 4264860469420169332246837)
                ·
                  refine ⟨399830669008140874898141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4264860469420169332246837 399830669008140874898141)
                  ·
                    rfl

theorem cell23_7008007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 5].length) (baseStart_7008007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008007 prefixEnd_7008007 := by exact prefixLift 7008007
  have htrace : WordTrace (prefixWord ++ tailWord_7008007) baseStart_7008007 baseEnd_7008007 := by
    simpa [prefixWord, tailWord_7008007, baseEnd_7008007] using wordTrace_append hprefix tailTrace_7008007
  have hstable : (prefixWord ++ tailWord_7008007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008007).length < 2 ^ (prefixWord ++ tailWord_7008007).sum := by decide
  have hdescent : baseEnd_7008007 < baseStart_7008007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008009 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 3]
def baseStart_7008009 : Nat := 118140960795 + 7008009 * 2 ^ 59
def prefixEnd_7008009 : Nat := 4983230072969 + 3 ^ 40 * 7008009 * 2
def baseEnd_7008009 : Nat := 3598477048034576866258259

theorem tailTrace_7008009 : CollatzResearch.WordTrace tailWord_7008009 prefixEnd_7008009 3598477048034576866258259 := by
  unfold tailWord_7008009
  simp only [CollatzResearch.WordTrace]
  refine ⟨255603086868187740494411081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170402057912125160329607387 255603086868187740494411081)
  ·
    refine ⟨191702315151140805370808311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255603086868187740494411081 191702315151140805370808311)
    ·
      refine ⟨287553472726711208056212467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191702315151140805370808311 287553472726711208056212467)
      ·
        refine ⟨431330209090066812084318701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287553472726711208056212467 431330209090066812084318701)
        ·
          refine ⟨161748828408775054531619513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431330209090066812084318701 161748828408775054531619513)
          ·
            refine ⟨121311621306581290898714635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161748828408775054531619513 121311621306581290898714635)
            ·
              refine ⟨181967431959871936348071953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121311621306581290898714635 181967431959871936348071953)
              ·
                refine ⟨136475573969903952261053965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181967431959871936348071953 136475573969903952261053965)
                ·
                  refine ⟨51178340238713982097895237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136475573969903952261053965 51178340238713982097895237)
                  ·
                    refine ⟨9595938794758871643355357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51178340238713982097895237 9595938794758871643355357)
                    ·
                      refine ⟨3598477048034576866258259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9595938794758871643355357 3598477048034576866258259)
                      ·
                        rfl

theorem cell23_7008009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_7008009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008009 prefixEnd_7008009 := by exact prefixLift 7008009
  have htrace : WordTrace (prefixWord ++ tailWord_7008009) baseStart_7008009 baseEnd_7008009 := by
    simpa [prefixWord, tailWord_7008009, baseEnd_7008009] using wordTrace_append hprefix tailTrace_7008009
  have hstable : (prefixWord ++ tailWord_7008009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008009).length < 2 ^ (prefixWord ++ tailWord_7008009).sum := by decide
  have hdescent : baseEnd_7008009 < baseStart_7008009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008023 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 2, 4, 2]
def baseStart_7008023 : Nat := 118140960795 + 7008023 * 2 ^ 59
def prefixEnd_7008023 : Nat := 4983230072969 + 3 ^ 40 * 7008023 * 2
def baseEnd_7008023 : Nat := 3598484236763739811483195

theorem tailTrace_7008023 : CollatzResearch.WordTrace tailWord_7008023 prefixEnd_7008023 3598484236763739811483195 := by
  unfold tailWord_7008023
  simp only [CollatzResearch.WordTrace]
  refine ⟨255603597490137020885420723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170402398326758013923613815 255603597490137020885420723)
  ·
    refine ⟨383405396235205531328131085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255603597490137020885420723 383405396235205531328131085)
    ·
      refine ⟨143777023588202074248049157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383405396235205531328131085 143777023588202074248049157)
      ·
        refine ⟨26958191922787888921509217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143777023588202074248049157 26958191922787888921509217)
        ·
          refine ⟨20218643942090916691131913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26958191922787888921509217 20218643942090916691131913)
          ·
            refine ⟨15163982956568187518348935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20218643942090916691131913 15163982956568187518348935)
            ·
              refine ⟨22745974434852281277523403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15163982956568187518348935 22745974434852281277523403)
              ·
                refine ⟨34118961652278421916285105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22745974434852281277523403 34118961652278421916285105)
                ·
                  refine ⟨25589221239208816437213829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34118961652278421916285105 25589221239208816437213829)
                  ·
                    refine ⟨4797978982351653081977593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25589221239208816437213829 4797978982351653081977593)
                    ·
                      refine ⟨3598484236763739811483195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4797978982351653081977593 3598484236763739811483195)
                      ·
                        rfl

theorem cell23_7008023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_7008023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008023 prefixEnd_7008023 := by exact prefixLift 7008023
  have htrace : WordTrace (prefixWord ++ tailWord_7008023) baseStart_7008023 baseEnd_7008023 := by
    simpa [prefixWord, tailWord_7008023, baseEnd_7008023] using wordTrace_append hprefix tailTrace_7008023
  have hstable : (prefixWord ++ tailWord_7008023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008023).length < 2 ^ (prefixWord ++ tailWord_7008023).sum := by decide
  have hdescent : baseEnd_7008023 < baseStart_7008023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008050 : List Nat := [3, 2, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_7008050 : Nat := 118140960795 + 7008050 * 2 ^ 59
def prefixEnd_7008050 : Nat := 4983230072969 + 3 ^ 40 * 7008050 * 2
def baseEnd_7008050 : Nat := 1199499366913803735281857

theorem tailTrace_7008050 : CollatzResearch.WordTrace tailWord_7008050 prefixEnd_7008050 1199499366913803735281857 := by
  unfold tailWord_7008050
  simp only [CollatzResearch.WordTrace]
  refine ⟨63901145565259801124163401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170403054840692802997769069 63901145565259801124163401)
  ·
    refine ⟨47925859173944850843122551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63901145565259801124163401 47925859173944850843122551)
    ·
      refine ⟨71888788760917276264683827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47925859173944850843122551 71888788760917276264683827)
      ·
        refine ⟨107833183141375914397025741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71888788760917276264683827 107833183141375914397025741)
        ·
          refine ⟨40437443678015967898884653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107833183141375914397025741 40437443678015967898884653)
          ·
            refine ⟨15164041379255987962081745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40437443678015967898884653 15164041379255987962081745)
            ·
              refine ⟨11373031034441990971561309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15164041379255987962081745 11373031034441990971561309)
              ·
                refine ⟨4264886637915746614335491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11373031034441990971561309 4264886637915746614335491)
                ·
                  refine ⟨6397329956873619921503237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264886637915746614335491 6397329956873619921503237)
                  ·
                    refine ⟨1199499366913803735281857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6397329956873619921503237 1199499366913803735281857)
                    ·
                      rfl

theorem cell23_7008050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_7008050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008050 prefixEnd_7008050 := by exact prefixLift 7008050
  have htrace : WordTrace (prefixWord ++ tailWord_7008050) baseStart_7008050 baseEnd_7008050 := by
    simpa [prefixWord, tailWord_7008050, baseEnd_7008050] using wordTrace_append hprefix tailTrace_7008050
  have hstable : (prefixWord ++ tailWord_7008050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008050).length < 2 ^ (prefixWord ++ tailWord_7008050).sum := by decide
  have hdescent : baseEnd_7008050 < baseStart_7008050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008063 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 6]
def baseStart_7008063 : Nat := 118140960795 + 7008063 * 2 ^ 59
def prefixEnd_7008063 : Nat := 4983230072969 + 3 ^ 40 * 7008063 * 2
def baseEnd_7008063 : Nat := 399833863998879961664779

theorem tailTrace_7008063 : CollatzResearch.WordTrace tailWord_7008063 prefixEnd_7008063 399833863998879961664779 := by
  unfold tailWord_7008063
  simp only [CollatzResearch.WordTrace]
  refine ⟨255605056409992107716876843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170403370939994738477917895 255605056409992107716876843)
  ·
    refine ⟨383407584614988161575315265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255605056409992107716876843 383407584614988161575315265)
    ·
      refine ⟨287555688461241121181486449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383407584614988161575315265 287555688461241121181486449)
      ·
        refine ⟨215666766345930840886114837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287555688461241121181486449 215666766345930840886114837)
        ·
          refine ⟨10109379672465508166536633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 215666766345930840886114837 10109379672465508166536633)
          ·
            refine ⟨7582034754349131124902475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10109379672465508166536633 7582034754349131124902475)
            ·
              refine ⟨11373052131523696687353713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7582034754349131124902475 11373052131523696687353713)
              ·
                refine ⟨8529789098642772515515285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11373052131523696687353713 8529789098642772515515285)
                ·
                  refine ⟨399833863998879961664779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8529789098642772515515285 399833863998879961664779)
                  ·
                    rfl

theorem cell23_7008063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 6].length) (baseStart_7008063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008063 prefixEnd_7008063 := by exact prefixLift 7008063
  have htrace : WordTrace (prefixWord ++ tailWord_7008063) baseStart_7008063 baseEnd_7008063 := by
    simpa [prefixWord, tailWord_7008063, baseEnd_7008063] using wordTrace_append hprefix tailTrace_7008063
  have hstable : (prefixWord ++ tailWord_7008063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008063).length < 2 ^ (prefixWord ++ tailWord_7008063).sum := by decide
  have hdescent : baseEnd_7008063 < baseStart_7008063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008073 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 3]
def baseStart_7008073 : Nat := 118140960795 + 7008073 * 2 ^ 59
def prefixEnd_7008073 : Nat := 4983230072969 + 3 ^ 40 * 7008073 * 2
def baseEnd_7008073 : Nat := 3598509910796464615857965

theorem tailTrace_7008073 : CollatzResearch.WordTrace tailWord_7008073 prefixEnd_7008073 3598509910796464615857965 := by
  unfold tailWord_7008073
  simp only [CollatzResearch.WordTrace]
  refine ⟨255605421139955879424740873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170403614093303919616493915 255605421139955879424740873)
  ·
    refine ⟨191704065854966909568555655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255605421139955879424740873 191704065854966909568555655)
    ·
      refine ⟨287556098782450364352833483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191704065854966909568555655 287556098782450364352833483)
      ·
        refine ⟨431334148173675546529250225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287556098782450364352833483 431334148173675546529250225)
        ·
          refine ⟨323500611130256659896937669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431334148173675546529250225 323500611130256659896937669)
          ·
            refine ⟨60656364586923123730675813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323500611130256659896937669 60656364586923123730675813)
            ·
              refine ⟨11373068360048085699501715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60656364586923123730675813 11373068360048085699501715)
              ·
                refine ⟨17059602540072128549252573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11373068360048085699501715 17059602540072128549252573)
                ·
                  refine ⟨6397350952527048205969715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17059602540072128549252573 6397350952527048205969715)
                  ·
                    refine ⟨9596026428790572308954573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6397350952527048205969715 9596026428790572308954573)
                    ·
                      refine ⟨3598509910796464615857965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9596026428790572308954573 3598509910796464615857965)
                      ·
                        rfl

theorem cell23_7008073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 3].length) (baseStart_7008073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008073 prefixEnd_7008073 := by exact prefixLift 7008073
  have htrace : WordTrace (prefixWord ++ tailWord_7008073) baseStart_7008073 baseEnd_7008073 := by
    simpa [prefixWord, tailWord_7008073, baseEnd_7008073] using wordTrace_append hprefix tailTrace_7008073
  have hstable : (prefixWord ++ tailWord_7008073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008073).length < 2 ^ (prefixWord ++ tailWord_7008073).sum := by decide
  have hdescent : baseEnd_7008073 < baseStart_7008073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008139 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 6]
def baseStart_7008139 : Nat := 118140960795 + 7008139 * 2 ^ 59
def prefixEnd_7008139 : Nat := 4983230072969 + 3 ^ 40 * 7008139 * 2
def baseEnd_7008139 : Nat := 3598543800519661357632661

theorem tailTrace_7008139 : CollatzResearch.WordTrace tailWord_7008139 prefixEnd_7008139 3598543800519661357632661 := by
  unfold tailWord_7008139
  simp only [CollatzResearch.WordTrace]
  refine ⟨255607828357716772696643471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170405218905144515131095647 255607828357716772696643471)
  ·
    refine ⟨383411742536575159044965207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255607828357716772696643471 383411742536575159044965207)
    ·
      refine ⟨575117613804862738567447811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383411742536575159044965207 575117613804862738567447811)
      ·
        refine ⟨862676420707294107851171717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575117613804862738567447811 862676420707294107851171717)
        ·
          refine ⟨161751828882617645222094697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 862676420707294107851171717 161751828882617645222094697)
          ·
            refine ⟨121313871661963233916571023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161751828882617645222094697 121313871661963233916571023)
            ·
              refine ⟨181970807492944850874856535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121313871661963233916571023 181970807492944850874856535)
              ·
                refine ⟨272956211239417276312284803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181970807492944850874856535 272956211239417276312284803)
                ·
                  refine ⟨409434316859125914468427205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272956211239417276312284803 409434316859125914468427205)
                  ·
                    refine ⟨76768934411086108962830101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409434316859125914468427205 76768934411086108962830101)
                    ·
                      refine ⟨3598543800519661357632661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76768934411086108962830101 3598543800519661357632661)
                      ·
                        rfl

theorem cell23_7008139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_7008139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008139 prefixEnd_7008139 := by exact prefixLift 7008139
  have htrace : WordTrace (prefixWord ++ tailWord_7008139) baseStart_7008139 baseEnd_7008139 := by
    simpa [prefixWord, tailWord_7008139, baseEnd_7008139] using wordTrace_append hprefix tailTrace_7008139
  have hstable : (prefixWord ++ tailWord_7008139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008139).length < 2 ^ (prefixWord ++ tailWord_7008139).sum := by decide
  have hdescent : baseEnd_7008139 < baseStart_7008139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008167 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_7008167 : Nat := 118140960795 + 7008167 * 2 ^ 59
def prefixEnd_7008167 : Nat := 4983230072969 + 3 ^ 40 * 7008167 * 2
def baseEnd_7008167 : Nat := 3598558177977987248082533

theorem tailTrace_7008167 : CollatzResearch.WordTrace tailWord_7008167 prefixEnd_7008167 3598558177977987248082533 := by
  unfold tailWord_7008167
  simp only [CollatzResearch.WordTrace]
  refine ⟨255608849601615333478662755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170405899734410222319108503 255608849601615333478662755)
  ·
    refine ⟨383413274402423000217994133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255608849601615333478662755 383413274402423000217994133)
    ·
      refine ⟨17972497237613578135218475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 383413274402423000217994133 17972497237613578135218475)
      ·
        refine ⟨26958745856420367202827713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17972497237613578135218475 26958745856420367202827713)
        ·
          refine ⟨20219059392315275402120785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26958745856420367202827713 20219059392315275402120785)
          ·
            refine ⟨15164294544236456551590589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20219059392315275402120785 15164294544236456551590589)
            ·
              refine ⟨5686610454088671206846471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15164294544236456551590589 5686610454088671206846471)
              ·
                refine ⟨8529915681133006810269707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5686610454088671206846471 8529915681133006810269707)
                ·
                  refine ⟨12794873521699510215404561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8529915681133006810269707 12794873521699510215404561)
                  ·
                    refine ⟨9596155141274632661553421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12794873521699510215404561 9596155141274632661553421)
                    ·
                      refine ⟨3598558177977987248082533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9596155141274632661553421 3598558177977987248082533)
                      ·
                        rfl

theorem cell23_7008167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_7008167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008167 prefixEnd_7008167 := by exact prefixLift 7008167
  have htrace : WordTrace (prefixWord ++ tailWord_7008167) baseStart_7008167 baseEnd_7008167 := by
    simpa [prefixWord, tailWord_7008167, baseEnd_7008167] using wordTrace_append hprefix tailTrace_7008167
  have hstable : (prefixWord ++ tailWord_7008167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008167).length < 2 ^ (prefixWord ++ tailWord_7008167).sum := by decide
  have hdescent : baseEnd_7008167 < baseStart_7008167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008181 : List Nat := [1, 3, 3, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_7008181 : Nat := 118140960795 + 7008181 * 2 ^ 59
def prefixEnd_7008181 : Nat := 4983230072969 + 3 ^ 40 * 7008181 * 2
def baseEnd_7008181 : Nat := 3598565366707150193307469

theorem tailTrace_7008181 : CollatzResearch.WordTrace tailWord_7008181 prefixEnd_7008181 3598565366707150193307469 := by
  unfold tailWord_7008181
  simp only [CollatzResearch.WordTrace]
  refine ⟨255609360223564613869672397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170406240149043075913114931 255609360223564613869672397)
  ·
    refine ⟨95853510083836730201127149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255609360223564613869672397 95853510083836730201127149)
    ·
      refine ⟨35945066281438773825422681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95853510083836730201127149 35945066281438773825422681)
      ·
        refine ⟨26958799711079080369067011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35945066281438773825422681 26958799711079080369067011)
        ·
          refine ⟨40438199566618620553600517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26958799711079080369067011 40438199566618620553600517)
          ·
            refine ⟨7582162418740991353800097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40438199566618620553600517 7582162418740991353800097)
            ·
              refine ⟨5686621814055743515350073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7582162418740991353800097 5686621814055743515350073)
              ·
                refine ⟨4264966360541807636512555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5686621814055743515350073 4264966360541807636512555)
                ·
                  refine ⟨6397449540812711454768833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264966360541807636512555 6397449540812711454768833)
                  ·
                    refine ⟨4798087155609533591076625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6397449540812711454768833 4798087155609533591076625)
                    ·
                      refine ⟨3598565366707150193307469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798087155609533591076625 3598565366707150193307469)
                      ·
                        rfl

theorem cell23_7008181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_7008181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008181 prefixEnd_7008181 := by exact prefixLift 7008181
  have htrace : WordTrace (prefixWord ++ tailWord_7008181) baseStart_7008181 baseEnd_7008181 := by
    simpa [prefixWord, tailWord_7008181, baseEnd_7008181] using wordTrace_append hprefix tailTrace_7008181
  have hstable : (prefixWord ++ tailWord_7008181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008181).length < 2 ^ (prefixWord ++ tailWord_7008181).sum := by decide
  have hdescent : baseEnd_7008181 < baseStart_7008181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008190 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_7008190 : Nat := 118140960795 + 7008190 * 2 ^ 59
def prefixEnd_7008190 : Nat := 4983230072969 + 3 ^ 40 * 7008190 * 2
def baseEnd_7008190 : Nat := 3598569988033040658094927

theorem tailTrace_7008190 : CollatzResearch.WordTrace tailWord_7008190 prefixEnd_7008190 3598569988033040658094927 := by
  unfold tailWord_7008190
  simp only [CollatzResearch.WordTrace]
  refine ⟨31951211060066501050843753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170406458987021338937833349 31951211060066501050843753)
  ·
    refine ⟨23963408295049875788132815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31951211060066501050843753 23963408295049875788132815)
    ·
      refine ⟨35945112442574813682199223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23963408295049875788132815 35945112442574813682199223)
      ·
        refine ⟨53917668663862220523298835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35945112442574813682199223 53917668663862220523298835)
        ·
          refine ⟨80876502995793330784948253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53917668663862220523298835 80876502995793330784948253)
          ·
            refine ⟨30328688623422499044355595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80876502995793330784948253 30328688623422499044355595)
            ·
              refine ⟨45493032935133748566533393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30328688623422499044355595 45493032935133748566533393)
              ·
                refine ⟨34119774701350311424900045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45493032935133748566533393 34119774701350311424900045)
                ·
                  refine ⟨12794915513006366784337517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34119774701350311424900045 12794915513006366784337517)
                  ·
                    refine ⟨4798093317377387544126569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12794915513006366784337517 4798093317377387544126569)
                    ·
                      refine ⟨3598569988033040658094927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798093317377387544126569 3598569988033040658094927)
                      ·
                        rfl

theorem cell23_7008190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_7008190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008190 prefixEnd_7008190 := by exact prefixLift 7008190
  have htrace : WordTrace (prefixWord ++ tailWord_7008190) baseStart_7008190 baseEnd_7008190 := by
    simpa [prefixWord, tailWord_7008190, baseEnd_7008190] using wordTrace_append hprefix tailTrace_7008190
  have hstable : (prefixWord ++ tailWord_7008190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008190).length < 2 ^ (prefixWord ++ tailWord_7008190).sum := by decide
  have hdescent : baseEnd_7008190 < baseStart_7008190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008216 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_7008216 : Nat := 118140960795 + 7008216 * 2 ^ 59
def prefixEnd_7008216 : Nat := 4983230072969 + 3 ^ 40 * 7008216 * 2
def baseEnd_7008216 : Nat := 3598583338530057556369807

theorem tailTrace_7008216 : CollatzResearch.WordTrace tailWord_7008216 prefixEnd_7008216 3598583338530057556369807 := by
  unfold tailWord_7008216
  simp only [CollatzResearch.WordTrace]
  refine ⟨127805318389218907423598251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170407091185625209898131001 127805318389218907423598251)
  ·
    refine ⟨191707977583828361135397377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127805318389218907423598251 191707977583828361135397377)
    ·
      refine ⟨143780983187871270851548033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191707977583828361135397377 143780983187871270851548033)
      ·
        refine ⟨107835737390903453138661025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143780983187871270851548033 107835737390903453138661025)
        ·
          refine ⟨80876803043177589853995769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107835737390903453138661025 80876803043177589853995769)
          ·
            refine ⟨60657602282383192390496827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80876803043177589853995769 60657602282383192390496827)
            ·
              refine ⟨90986403423574788585745241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60657602282383192390496827 90986403423574788585745241)
              ·
                refine ⟨68239802567681091439308931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90986403423574788585745241 68239802567681091439308931)
                ·
                  refine ⟨102359703851521637158963397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68239802567681091439308931 102359703851521637158963397)
                  ·
                    refine ⟨19192444472160306967305637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102359703851521637158963397 19192444472160306967305637)
                    ·
                      refine ⟨3598583338530057556369807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19192444472160306967305637 3598583338530057556369807)
                      ·
                        rfl

theorem cell23_7008216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_7008216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008216 prefixEnd_7008216 := by exact prefixLift 7008216
  have htrace : WordTrace (prefixWord ++ tailWord_7008216) baseStart_7008216 baseEnd_7008216 := by
    simpa [prefixWord, tailWord_7008216, baseEnd_7008216] using wordTrace_append hprefix tailTrace_7008216
  have hstable : (prefixWord ++ tailWord_7008216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008216).length < 2 ^ (prefixWord ++ tailWord_7008216).sum := by decide
  have hdescent : baseEnd_7008216 < baseStart_7008216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008253 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_7008253 : Nat := 118140960795 + 7008253 * 2 ^ 59
def prefixEnd_7008253 : Nat := 4983230072969 + 3 ^ 40 * 7008253 * 2
def baseEnd_7008253 : Nat := 3598602337314273911607137

theorem tailTrace_7008253 : CollatzResearch.WordTrace tailWord_7008253 prefixEnd_7008253 3598602337314273911607137 := by
  unfold tailWord_7008253
  simp only [CollatzResearch.WordTrace]
  refine ⟨255611986279303770166293413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170407990852869180110862275 255611986279303770166293413)
  ·
    refine ⟨47927247427369456906180015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255611986279303770166293413 47927247427369456906180015)
    ·
      refine ⟨71890871141054185359270023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47927247427369456906180015 71890871141054185359270023)
      ·
        refine ⟨107836306711581278038905035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71890871141054185359270023 107836306711581278038905035)
        ·
          refine ⟨161754460067371917058357553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107836306711581278038905035 161754460067371917058357553)
          ·
            refine ⟨121315845050528937793768165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161754460067371917058357553 121315845050528937793768165)
            ·
              refine ⟨22746720946974175836331531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121315845050528937793768165 22746720946974175836331531)
              ·
                refine ⟨34120081420461263754497297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22746720946974175836331531 34120081420461263754497297)
                ·
                  refine ⟨25590061065345947815872973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34120081420461263754497297 25590061065345947815872973)
                  ·
                    refine ⟨9596272899504730430952365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25590061065345947815872973 9596272899504730430952365)
                    ·
                      refine ⟨3598602337314273911607137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9596272899504730430952365 3598602337314273911607137)
                      ·
                        rfl

theorem cell23_7008253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_7008253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008253 prefixEnd_7008253 := by exact prefixLift 7008253
  have htrace : WordTrace (prefixWord ++ tailWord_7008253) baseStart_7008253 baseEnd_7008253 := by
    simpa [prefixWord, tailWord_7008253, baseEnd_7008253] using wordTrace_append hprefix tailTrace_7008253
  have hstable : (prefixWord ++ tailWord_7008253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008253).length < 2 ^ (prefixWord ++ tailWord_7008253).sum := by decide
  have hdescent : baseEnd_7008253 < baseStart_7008253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008254 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_7008254 : Nat := 118140960795 + 7008254 * 2 ^ 59
def prefixEnd_7008254 : Nat := 4983230072969 + 3 ^ 40 * 7008254 * 2
def baseEnd_7008254 : Nat := 3598602850794928407694633

theorem tailTrace_7008254 : CollatzResearch.WordTrace tailWord_7008254 prefixEnd_7008254 3598602850794928407694633 := by
  unfold tailWord_7008254
  simp only [CollatzResearch.WordTrace]
  refine ⟨31951502844037518417134977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170408015168200098224719877 31951502844037518417134977)
  ·
    refine ⟨23963627133028138812851233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31951502844037518417134977 23963627133028138812851233)
    ·
      refine ⟨17972720349771104109638425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23963627133028138812851233 17972720349771104109638425)
      ·
        refine ⟨13479540262328328082228819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17972720349771104109638425 13479540262328328082228819)
        ·
          refine ⟨20219310393492492123343229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13479540262328328082228819 20219310393492492123343229)
          ·
            refine ⟨7582241397559684546253711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20219310393492492123343229 7582241397559684546253711)
            ·
              refine ⟨11373362096339526819380567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7582241397559684546253711 11373362096339526819380567)
              ·
                refine ⟨17060043144509290229070851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11373362096339526819380567 17060043144509290229070851)
                ·
                  refine ⟨25590064716763935343606277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17060043144509290229070851 25590064716763935343606277)
                  ·
                    refine ⟨4798137134393237876926177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25590064716763935343606277 4798137134393237876926177)
                    ·
                      refine ⟨3598602850794928407694633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798137134393237876926177 3598602850794928407694633)
                      ·
                        rfl

theorem cell23_7008254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_7008254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008254 prefixEnd_7008254 := by exact prefixLift 7008254
  have htrace : WordTrace (prefixWord ++ tailWord_7008254) baseStart_7008254 baseEnd_7008254 := by
    simpa [prefixWord, tailWord_7008254, baseEnd_7008254] using wordTrace_append hprefix tailTrace_7008254
  have hstable : (prefixWord ++ tailWord_7008254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008254).length < 2 ^ (prefixWord ++ tailWord_7008254).sum := by decide
  have hdescent : baseEnd_7008254 < baseStart_7008254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008256 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 6, 5]
def baseStart_7008256 : Nat := 118140960795 + 7008256 * 2 ^ 59
def prefixEnd_7008256 : Nat := 4983230072969 + 3 ^ 40 * 7008256 * 2
def baseEnd_7008256 : Nat := 1199534625918745799956541

theorem tailTrace_7008256 : CollatzResearch.WordTrace tailWord_7008256 prefixEnd_7008256 1199534625918745799956541 := by
  unfold tailWord_7008256
  simp only [CollatzResearch.WordTrace]
  refine ⟨127806047849146450839326311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170408063798861934452435081 127806047849146450839326311)
  ·
    refine ⟨191709071773719676258989467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127806047849146450839326311 191709071773719676258989467)
    ·
      refine ⟨287563607660579514388484201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191709071773719676258989467 287563607660579514388484201)
      ·
        refine ⟨215672705745434635791363151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287563607660579514388484201 215672705745434635791363151)
        ·
          refine ⟨323509058618151953687044727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215672705745434635791363151 323509058618151953687044727)
          ·
            refine ⟨485263587927227930530567091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323509058618151953687044727 485263587927227930530567091)
            ·
              refine ⟨727895381890841895795850637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485263587927227930530567091 727895381890841895795850637)
              ·
                refine ⟨272960768209065710923443989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 727895381890841895795850637 272960768209065710923443989)
                ·
                  refine ⟨12795036009799955199536437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 272960768209065710923443989 12795036009799955199536437)
                  ·
                    refine ⟨1199534625918745799956541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12795036009799955199536437 1199534625918745799956541)
                    ·
                      rfl

theorem cell23_7008256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_7008256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008256 prefixEnd_7008256 := by exact prefixLift 7008256
  have htrace : WordTrace (prefixWord ++ tailWord_7008256) baseStart_7008256 baseEnd_7008256 := by
    simpa [prefixWord, tailWord_7008256, baseEnd_7008256] using wordTrace_append hprefix tailTrace_7008256
  have hstable : (prefixWord ++ tailWord_7008256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008256).length < 2 ^ (prefixWord ++ tailWord_7008256).sum := by decide
  have hdescent : baseEnd_7008256 < baseStart_7008256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008277 : List Nat := [1, 3, 2, 1, 5, 2, 1, 3, 5]
def baseStart_7008277 : Nat := 118140960795 + 7008277 * 2 ^ 59
def prefixEnd_7008277 : Nat := 4983230072969 + 3 ^ 40 * 7008277 * 2
def baseEnd_7008277 : Nat := 399846073427775757523003

theorem tailTrace_7008277 : CollatzResearch.WordTrace tailWord_7008277 prefixEnd_7008277 399846073427775757523003 := by
  unfold tailWord_7008277
  simp only [CollatzResearch.WordTrace]
  refine ⟨255612861631216822265167085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170408574420811214843444723 255612861631216822265167085)
  ·
    refine ⟨95854823111706308349437657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255612861631216822265167085 95854823111706308349437657)
    ·
      refine ⟨71891117333779731262078243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95854823111706308349437657 71891117333779731262078243)
      ·
        refine ⟨107836676000669596893117365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71891117333779731262078243 107836676000669596893117365)
        ·
          refine ⟨10109688375062774708729753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107836676000669596893117365 10109688375062774708729753)
          ·
            refine ⟨7582266281297081031547315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10109688375062774708729753 7582266281297081031547315)
            ·
              refine ⟨11373399421945621547320973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7582266281297081031547315 11373399421945621547320973)
              ·
                refine ⟨4265024783229608080245365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11373399421945621547320973 4265024783229608080245365)
                ·
                  refine ⟨399846073427775757523003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265024783229608080245365 399846073427775757523003)
                  ·
                    rfl

theorem cell23_7008277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_7008277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008277 prefixEnd_7008277 := by exact prefixLift 7008277
  have htrace : WordTrace (prefixWord ++ tailWord_7008277) baseStart_7008277 baseEnd_7008277 := by
    simpa [prefixWord, tailWord_7008277, baseEnd_7008277] using wordTrace_append hprefix tailTrace_7008277
  have hstable : (prefixWord ++ tailWord_7008277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008277).length < 2 ^ (prefixWord ++ tailWord_7008277).sum := by decide
  have hdescent : baseEnd_7008277 < baseStart_7008277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008293 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_7008293 : Nat := 118140960795 + 7008293 * 2 ^ 59
def prefixEnd_7008293 : Nat := 4983230072969 + 3 ^ 40 * 7008293 * 2
def baseEnd_7008293 : Nat := 3598622876540453755106953

theorem tailTrace_7008293 : CollatzResearch.WordTrace tailWord_7008293 prefixEnd_7008293 3598622876540453755106953 := by
  unfold tailWord_7008293
  simp only [CollatzResearch.WordTrace]
  refine ⟨255613445199158856997749533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170408963466105904665166355 255613445199158856997749533)
  ·
    refine ⟨95855041949684571374156075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255613445199158856997749533 95855041949684571374156075)
    ·
      refine ⟨143782562924526857061234113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95855041949684571374156075 143782562924526857061234113)
      ·
        refine ⟨107836922193395142795925585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143782562924526857061234113 107836922193395142795925585)
        ·
          refine ⟨80877691645046357096944189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107836922193395142795925585 80877691645046357096944189)
          ·
            refine ⟨30329134366892383911354071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80877691645046357096944189 30329134366892383911354071)
            ·
              refine ⟨45493701550338575867031107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30329134366892383911354071 45493701550338575867031107)
              ·
                refine ⟨68240552325507863800546661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45493701550338575867031107 68240552325507863800546661)
                ·
                  refine ⟨12795103561032724462602499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68240552325507863800546661 12795103561032724462602499)
                  ·
                    refine ⟨19192655341549086693903749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12795103561032724462602499 19192655341549086693903749)
                    ·
                      refine ⟨3598622876540453755106953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19192655341549086693903749 3598622876540453755106953)
                      ·
                        rfl

theorem cell23_7008293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_7008293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008293 prefixEnd_7008293 := by exact prefixLift 7008293
  have htrace : WordTrace (prefixWord ++ tailWord_7008293) baseStart_7008293 baseEnd_7008293 := by
    simpa [prefixWord, tailWord_7008293, baseEnd_7008293] using wordTrace_append hprefix tailTrace_7008293
  have hstable : (prefixWord ++ tailWord_7008293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008293).length < 2 ^ (prefixWord ++ tailWord_7008293).sum := by decide
  have hdescent : baseEnd_7008293 < baseStart_7008293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008303 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 3, 4]
def baseStart_7008303 : Nat := 118140960795 + 7008303 * 2 ^ 59
def prefixEnd_7008303 : Nat := 4983230072969 + 3 ^ 40 * 7008303 * 2
def baseEnd_7008303 : Nat := 1199542670448999571993969

theorem tailTrace_7008303 : CollatzResearch.WordTrace tailWord_7008303 prefixEnd_7008303 1199542670448999571993969 := by
  unfold tailWord_7008303
  simp only [CollatzResearch.WordTrace]
  refine ⟨255613809929122628705613563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170409206619415085803742375 255613809929122628705613563)
  ·
    refine ⟨383420714893683943058420345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255613809929122628705613563 383420714893683943058420345)
    ·
      refine ⟨287565536170262957293815259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383420714893683943058420345 287565536170262957293815259)
      ·
        refine ⟨431348304255394435940722889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287565536170262957293815259 431348304255394435940722889)
        ·
          refine ⟨323511228191545826955542167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431348304255394435940722889 323511228191545826955542167)
          ·
            refine ⟨485266842287318740433313251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323511228191545826955542167 485266842287318740433313251)
            ·
              refine ⟨727900263430978110649969877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485266842287318740433313251 727900263430978110649969877)
              ·
                refine ⟨17060162424163549468358669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 727900263430978110649969877 17060162424163549468358669)
                ·
                  refine ⟨6397560909061331050634501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17060162424163549468358669 6397560909061331050634501)
                  ·
                    refine ⟨1199542670448999571993969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6397560909061331050634501 1199542670448999571993969)
                    ·
                      rfl

theorem cell23_7008303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 4].length) (baseStart_7008303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008303 prefixEnd_7008303 := by exact prefixLift 7008303
  have htrace : WordTrace (prefixWord ++ tailWord_7008303) baseStart_7008303 baseEnd_7008303 := by
    simpa [prefixWord, tailWord_7008303, baseEnd_7008303] using wordTrace_append hprefix tailTrace_7008303
  have hstable : (prefixWord ++ tailWord_7008303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008303).length < 2 ^ (prefixWord ++ tailWord_7008303).sum := by decide
  have hdescent : baseEnd_7008303 < baseStart_7008303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008310 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_7008310 : Nat := 118140960795 + 7008310 * 2 ^ 59
def prefixEnd_7008310 : Nat := 4983230072969 + 3 ^ 40 * 7008310 * 2
def baseEnd_7008310 : Nat := 3598631605711580188594375

theorem tailTrace_7008310 : CollatzResearch.WordTrace tailWord_7008310 prefixEnd_7008310 3598631605711580188594375 := by
  unfold tailWord_7008310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15975879077506079306319899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170409376826731512600745589 15975879077506079306319899)
  ·
    refine ⟨23963818616259118959479849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15975879077506079306319899 23963818616259118959479849)
    ·
      refine ⟨17972863962194339219609887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23963818616259118959479849 17972863962194339219609887)
      ·
        refine ⟨26959295943291508829414831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17972863962194339219609887 26959295943291508829414831)
        ·
          refine ⟨40438943914937263244122247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26959295943291508829414831 40438943914937263244122247)
          ·
            refine ⟨60658415872405894866183371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40438943914937263244122247 60658415872405894866183371)
            ·
              refine ⟨90987623808608842299275057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60658415872405894866183371 90987623808608842299275057)
              ·
                refine ⟨68240717856456631724456293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90987623808608842299275057 68240717856456631724456293)
                ·
                  refine ⟨12795134598085618448335555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68240717856456631724456293 12795134598085618448335555)
                  ·
                    refine ⟨19192701897128427672503333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12795134598085618448335555 19192701897128427672503333)
                    ·
                      refine ⟨3598631605711580188594375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19192701897128427672503333 3598631605711580188594375)
                      ·
                        rfl

theorem cell23_7008310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_7008310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008310 prefixEnd_7008310 := by exact prefixLift 7008310
  have htrace : WordTrace (prefixWord ++ tailWord_7008310) baseStart_7008310 baseEnd_7008310 := by
    simpa [prefixWord, tailWord_7008310, baseEnd_7008310] using wordTrace_append hprefix tailTrace_7008310
  have hstable : (prefixWord ++ tailWord_7008310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008310).length < 2 ^ (prefixWord ++ tailWord_7008310).sum := by decide
  have hdescent : baseEnd_7008310 < baseStart_7008310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008336 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_7008336 : Nat := 118140960795 + 7008336 * 2 ^ 59
def prefixEnd_7008336 : Nat := 4983230072969 + 3 ^ 40 * 7008336 * 2
def baseEnd_7008336 : Nat := 3598644956208597086869255

theorem tailTrace_7008336 : CollatzResearch.WordTrace tailWord_7008336 prefixEnd_7008336 3598644956208597086869255 := by
  unfold tailWord_7008336
  simp only [CollatzResearch.WordTrace]
  refine ⟨127807506769001537670782431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170410009025335383561043241 127807506769001537670782431)
  ·
    refine ⟨191711260153502306506173647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127807506769001537670782431 191711260153502306506173647)
    ·
      refine ⟨287566890230253459759260471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191711260153502306506173647 287566890230253459759260471)
      ·
        refine ⟨431350335345380189638890707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287566890230253459759260471 431350335345380189638890707)
        ·
          refine ⟨647025503018070284458336061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431350335345380189638890707 647025503018070284458336061)
          ·
            refine ⟨242634563631776356671876023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647025503018070284458336061 242634563631776356671876023)
            ·
              refine ⟨363951845447664535007814035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242634563631776356671876023 363951845447664535007814035)
              ·
                refine ⟨545927768171496802511721053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363951845447664535007814035 545927768171496802511721053)
                ·
                  refine ⟨204722913064311300941895395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545927768171496802511721053 204722913064311300941895395)
                  ·
                    refine ⟨307084369596466951412843093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204722913064311300941895395 307084369596466951412843093)
                    ·
                      refine ⟨3598644956208597086869255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 307084369596466951412843093 3598644956208597086869255)
                      ·
                        rfl

theorem cell23_7008336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_7008336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008336 prefixEnd_7008336 := by exact prefixLift 7008336
  have htrace : WordTrace (prefixWord ++ tailWord_7008336) baseStart_7008336 baseEnd_7008336 := by
    simpa [prefixWord, tailWord_7008336, baseEnd_7008336] using wordTrace_append hprefix tailTrace_7008336
  have hstable : (prefixWord ++ tailWord_7008336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008336).length < 2 ^ (prefixWord ++ tailWord_7008336).sum := by decide
  have hdescent : baseEnd_7008336 < baseStart_7008336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008377 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 3]
def baseStart_7008377 : Nat := 118140960795 + 7008377 * 2 ^ 59
def prefixEnd_7008377 : Nat := 4983230072969 + 3 ^ 40 * 7008377 * 2
def baseEnd_7008377 : Nat := 3598666008915431426456567

theorem tailTrace_7008377 : CollatzResearch.WordTrace tailWord_7008377 prefixEnd_7008377 3598666008915431426456567 := by
  unfold tailWord_7008377
  simp only [CollatzResearch.WordTrace]
  refine ⟨255616508930854539343807385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170411005953903026229204923 255616508930854539343807385)
  ·
    refine ⟨191712381698140904507855539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255616508930854539343807385 191712381698140904507855539)
    ·
      refine ⟨287568572547211356761783309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191712381698140904507855539 287568572547211356761783309)
      ·
        refine ⟨107838214705204258785668741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287568572547211356761783309 107838214705204258785668741)
        ·
          refine ⟨20219665257225798522312889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107838214705204258785668741 20219665257225798522312889)
          ·
            refine ⟨15164748942919348891734667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20219665257225798522312889 15164748942919348891734667)
            ·
              refine ⟨22747123414379023337602001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15164748942919348891734667 22747123414379023337602001)
              ·
                refine ⟨17060342560784267503201501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22747123414379023337602001 17060342560784267503201501)
                ·
                  refine ⟨6397628460294100313700563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17060342560784267503201501 6397628460294100313700563)
                  ·
                    refine ⟨9596442690441150470550845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6397628460294100313700563 9596442690441150470550845)
                    ·
                      refine ⟨3598666008915431426456567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9596442690441150470550845 3598666008915431426456567)
                      ·
                        rfl

theorem cell23_7008377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_7008377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008377 prefixEnd_7008377 := by exact prefixLift 7008377
  have htrace : WordTrace (prefixWord ++ tailWord_7008377) baseStart_7008377 baseEnd_7008377 := by
    simpa [prefixWord, tailWord_7008377, baseEnd_7008377] using wordTrace_append hprefix tailTrace_7008377
  have hstable : (prefixWord ++ tailWord_7008377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008377).length < 2 ^ (prefixWord ++ tailWord_7008377).sum := by decide
  have hdescent : baseEnd_7008377 < baseStart_7008377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008387 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 2, 3, 2]
def baseStart_7008387 : Nat := 118140960795 + 7008387 * 2 ^ 59
def prefixEnd_7008387 : Nat := 4983230072969 + 3 ^ 40 * 7008387 * 2
def baseEnd_7008387 : Nat := 3598671143721976387331521

theorem tailTrace_7008387 : CollatzResearch.WordTrace tailWord_7008387 prefixEnd_7008387 3598671143721976387331521 := by
  unfold tailWord_7008387
  simp only [CollatzResearch.WordTrace]
  refine ⟨255616873660818311051671415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170411249107212207367780943 255616873660818311051671415)
  ·
    refine ⟨383425310491227466577507123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255616873660818311051671415 383425310491227466577507123)
    ·
      refine ⟨575137965736841199866260685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383425310491227466577507123 575137965736841199866260685)
      ·
        refine ⟨215676737151315449949847757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575137965736841199866260685 215676737151315449949847757)
        ·
          refine ⟨80878776431743293731192909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215676737151315449949847757 80878776431743293731192909)
          ·
            refine ⟨30329541161903735149197341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80878776431743293731192909 30329541161903735149197341)
            ·
              refine ⟨11373577935713900680949003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30329541161903735149197341 11373577935713900680949003)
              ·
                refine ⟨17060366903570851021423505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11373577935713900680949003 17060366903570851021423505)
                ·
                  refine ⟨12795275177678138266067629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17060366903570851021423505 12795275177678138266067629)
                  ·
                    refine ⟨4798228191629301849775361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12795275177678138266067629 4798228191629301849775361)
                    ·
                      refine ⟨3598671143721976387331521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798228191629301849775361 3598671143721976387331521)
                      ·
                        rfl

theorem cell23_7008387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_7008387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008387 prefixEnd_7008387 := by exact prefixLift 7008387
  have htrace : WordTrace (prefixWord ++ tailWord_7008387) baseStart_7008387 baseEnd_7008387 := by
    simpa [prefixWord, tailWord_7008387, baseEnd_7008387] using wordTrace_append hprefix tailTrace_7008387
  have hstable : (prefixWord ++ tailWord_7008387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008387).length < 2 ^ (prefixWord ++ tailWord_7008387).sum := by decide
  have hdescent : baseEnd_7008387 < baseStart_7008387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008393 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 1, 6]
def baseStart_7008393 : Nat := 118140960795 + 7008393 * 2 ^ 59
def prefixEnd_7008393 : Nat := 4983230072969 + 3 ^ 40 * 7008393 * 2
def baseEnd_7008393 : Nat := 1199558074868634454618831

theorem tailTrace_7008393 : CollatzResearch.WordTrace tailWord_7008393 prefixEnd_7008393 1199558074868634454618831 := by
  unfold tailWord_7008393
  simp only [CollatzResearch.WordTrace]
  refine ⟨255617092498796574076389833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170411394999197716050926555 255617092498796574076389833)
  ·
    refine ⟨191712819374097430557292375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255617092498796574076389833 191712819374097430557292375)
    ·
      refine ⟨287569229061146145835938563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191712819374097430557292375 287569229061146145835938563)
      ·
        refine ⟨431353843591719218753907845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287569229061146145835938563 431353843591719218753907845)
        ·
          refine ⟨80878845673447353516357721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431353843591719218753907845 80878845673447353516357721)
          ·
            refine ⟨60659134255085515137268291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80878845673447353516357721 60659134255085515137268291)
            ·
              refine ⟨90988701382628272705902437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60659134255085515137268291 90988701382628272705902437)
              ·
                refine ⟨17060381509242801132356707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90988701382628272705902437 17060381509242801132356707)
                ·
                  refine ⟨25590572263864201698535061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17060381509242801132356707 25590572263864201698535061)
                  ·
                    refine ⟨1199558074868634454618831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25590572263864201698535061 1199558074868634454618831)
                    ·
                      rfl

theorem cell23_7008393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_7008393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008393 prefixEnd_7008393 := by exact prefixLift 7008393
  have htrace : WordTrace (prefixWord ++ tailWord_7008393) baseStart_7008393 baseEnd_7008393 := by
    simpa [prefixWord, tailWord_7008393, baseEnd_7008393] using wordTrace_append hprefix tailTrace_7008393
  have hstable : (prefixWord ++ tailWord_7008393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008393).length < 2 ^ (prefixWord ++ tailWord_7008393).sum := by decide
  have hdescent : baseEnd_7008393 < baseStart_7008393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008394 : List Nat := [3, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3]
def baseStart_7008394 : Nat := 118140960795 + 7008394 * 2 ^ 59
def prefixEnd_7008394 : Nat := 4983230072969 + 3 ^ 40 * 7008394 * 2
def baseEnd_7008394 : Nat := 3598674738086557859943989

theorem tailTrace_7008394 : CollatzResearch.WordTrace tailWord_7008394 prefixEnd_7008394 3598674738086557859943989 := by
  unfold tailWord_7008394
  simp only [CollatzResearch.WordTrace]
  refine ⟨63904282242948237811794059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170411419314528634164784157 63904282242948237811794059)
  ·
    refine ⟨95856423364422356717691089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63904282242948237811794059 95856423364422356717691089)
    ·
      refine ⟨71892317523316767538268317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95856423364422356717691089 71892317523316767538268317)
      ·
        refine ⟨26959619071243787826850619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71892317523316767538268317 26959619071243787826850619)
        ·
          refine ⟨40439428606865681740275929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26959619071243787826850619 40439428606865681740275929)
          ·
            refine ⟨30329571455149261305206947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40439428606865681740275929 30329571455149261305206947)
            ·
              refine ⟨45494357182723891957810421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30329571455149261305206947 45494357182723891957810421)
              ·
                refine ⟨4265095985880364871044727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45494357182723891957810421 4265095985880364871044727)
                ·
                  refine ⟨6397643978820547306567091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265095985880364871044727 6397643978820547306567091)
                  ·
                    refine ⟨9596465968230820959850637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6397643978820547306567091 9596465968230820959850637)
                    ·
                      refine ⟨3598674738086557859943989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9596465968230820959850637 3598674738086557859943989)
                      ·
                        rfl

theorem cell23_7008394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_7008394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008394 prefixEnd_7008394 := by exact prefixLift 7008394
  have htrace : WordTrace (prefixWord ++ tailWord_7008394) baseStart_7008394 baseEnd_7008394 := by
    simpa [prefixWord, tailWord_7008394, baseEnd_7008394] using wordTrace_append hprefix tailTrace_7008394
  have hstable : (prefixWord ++ tailWord_7008394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008394).length < 2 ^ (prefixWord ++ tailWord_7008394).sum := by decide
  have hdescent : baseEnd_7008394 < baseStart_7008394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008400 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 4]
def baseStart_7008400 : Nat := 118140960795 + 7008400 * 2 ^ 59
def prefixEnd_7008400 : Nat := 4983230072969 + 3 ^ 40 * 7008400 * 2
def baseEnd_7008400 : Nat := 3598677818970484836468961

theorem tailTrace_7008400 : CollatzResearch.WordTrace tailWord_7008400 prefixEnd_7008400 3598677818970484836468961 := by
  unfold tailWord_7008400
  simp only [CollatzResearch.WordTrace]
  refine ⟨127808673904885607135947327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170411565206514142847929769 127808673904885607135947327)
  ·
    refine ⟨191713010857328410703920991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127808673904885607135947327 191713010857328410703920991)
    ·
      refine ⟨287569516285992616055881487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191713010857328410703920991 287569516285992616055881487)
      ·
        refine ⟨431354274428988924083822231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287569516285992616055881487 431354274428988924083822231)
        ·
          refine ⟨647031411643483386125733347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431354274428988924083822231 647031411643483386125733347)
          ·
            refine ⟨970547117465225079188600021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647031411643483386125733347 970547117465225079188600021)
            ·
              refine ⟨22747198065591212793482813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 970547117465225079188600021 22747198065591212793482813)
              ·
                refine ⟨8530199274596704797556055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22747198065591212793482813 8530199274596704797556055)
                ·
                  refine ⟨12795298911895057196334083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8530199274596704797556055 12795298911895057196334083)
                  ·
                    refine ⟨19192948367842585794501125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12795298911895057196334083 19192948367842585794501125)
                    ·
                      refine ⟨3598677818970484836468961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19192948367842585794501125 3598677818970484836468961)
                      ·
                        rfl

theorem cell23_7008400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 4].length) (baseStart_7008400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008400 prefixEnd_7008400 := by exact prefixLift 7008400
  have htrace : WordTrace (prefixWord ++ tailWord_7008400) baseStart_7008400 baseEnd_7008400 := by
    simpa [prefixWord, tailWord_7008400, baseEnd_7008400] using wordTrace_append hprefix tailTrace_7008400
  have hstable : (prefixWord ++ tailWord_7008400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008400).length < 2 ^ (prefixWord ++ tailWord_7008400).sum := by decide
  have hdescent : baseEnd_7008400 < baseStart_7008400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008403 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 5]
def baseStart_7008403 : Nat := 118140960795 + 7008403 * 2 ^ 59
def prefixEnd_7008403 : Nat := 4983230072969 + 3 ^ 40 * 7008403 * 2
def baseEnd_7008403 : Nat := 3598679359412448324731447

theorem tailTrace_7008403 : CollatzResearch.WordTrace tailWord_7008403 prefixEnd_7008403 3598679359412448324731447 := by
  unfold tailWord_7008403
  simp only [CollatzResearch.WordTrace]
  refine ⟨255617457228760345784253863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170411638152506897189502575 255617457228760345784253863)
  ·
    refine ⟨383426185843140518676380795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255617457228760345784253863 383426185843140518676380795)
    ·
      refine ⟨575139278764710778014571193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383426185843140518676380795 575139278764710778014571193)
      ·
        refine ⟨431354459073533083510928395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575139278764710778014571193 431354459073533083510928395)
        ·
          refine ⟨647031688610299625266392593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431354459073533083510928395 647031688610299625266392593)
          ·
            refine ⟨485273766457724718949794445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647031688610299625266392593 485273766457724718949794445)
            ·
              refine ⟨181977662421646769606172917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485273766457724718949794445 181977662421646769606172917)
              ·
                refine ⟨17060405852029384650578711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181977662421646769606172917 17060405852029384650578711)
                ·
                  refine ⟨25590608778044076975868067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17060405852029384650578711 25590608778044076975868067)
                  ·
                    refine ⟨38385913167066115463802101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25590608778044076975868067 38385913167066115463802101)
                    ·
                      refine ⟨3598679359412448324731447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38385913167066115463802101 3598679359412448324731447)
                      ·
                        rfl

theorem cell23_7008403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_7008403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008403 prefixEnd_7008403 := by exact prefixLift 7008403
  have htrace : WordTrace (prefixWord ++ tailWord_7008403) baseStart_7008403 baseEnd_7008403 := by
    simpa [prefixWord, tailWord_7008403, baseEnd_7008403] using wordTrace_append hprefix tailTrace_7008403
  have hstable : (prefixWord ++ tailWord_7008403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008403).length < 2 ^ (prefixWord ++ tailWord_7008403).sum := by decide
  have hdescent : baseEnd_7008403 < baseStart_7008403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008463 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_7008463 : Nat := 118140960795 + 7008463 * 2 ^ 59
def prefixEnd_7008463 : Nat := 4983230072969 + 3 ^ 40 * 7008463 * 2
def baseEnd_7008463 : Nat := 3598710168251718089981171

theorem tailTrace_7008463 : CollatzResearch.WordTrace tailWord_7008463 prefixEnd_7008463 3598710168251718089981171 := by
  unfold tailWord_7008463
  simp only [CollatzResearch.WordTrace]
  refine ⟨255619645608542976031438043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170413097072361984020958695 255619645608542976031438043)
  ·
    refine ⟨383429468412814464047157065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255619645608542976031438043 383429468412814464047157065)
    ·
      refine ⟨287572101309610848035367799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383429468412814464047157065 287572101309610848035367799)
      ·
        refine ⟨431358151964416272053051699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287572101309610848035367799 431358151964416272053051699)
        ·
          refine ⟨647037227946624408079577549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431358151964416272053051699 647037227946624408079577549)
          ·
            refine ⟨242638960479984153029841581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647037227946624408079577549 242638960479984153029841581)
            ·
              refine ⟨90989610179994057386190593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242638960479984153029841581 90989610179994057386190593)
              ·
                refine ⟨68242207634995543039642945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90989610179994057386190593 68242207634995543039642945)
                ·
                  refine ⟨51181655726246657279732209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68242207634995543039642945 51181655726246657279732209)
                  ·
                    refine ⟨38386241794684992959799157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51181655726246657279732209 38386241794684992959799157)
                    ·
                      refine ⟨3598710168251718089981171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38386241794684992959799157 3598710168251718089981171)
                      ·
                        rfl

theorem cell23_7008463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_7008463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008463 prefixEnd_7008463 := by exact prefixLift 7008463
  have htrace : WordTrace (prefixWord ++ tailWord_7008463) baseStart_7008463 baseEnd_7008463 := by
    simpa [prefixWord, tailWord_7008463, baseEnd_7008463] using wordTrace_append hprefix tailTrace_7008463
  have hstable : (prefixWord ++ tailWord_7008463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008463).length < 2 ^ (prefixWord ++ tailWord_7008463).sum := by decide
  have hdescent : baseEnd_7008463 < baseStart_7008463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008541 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_7008541 : Nat := 118140960795 + 7008541 * 2 ^ 59
def prefixEnd_7008541 : Nat := 4983230072969 + 3 ^ 40 * 7008541 * 2
def baseEnd_7008541 : Nat := 3598750219742768784805813

theorem tailTrace_7008541 : CollatzResearch.WordTrace tailWord_7008541 prefixEnd_7008541 3598750219742768784805813 := by
  unfold tailWord_7008541
  simp only [CollatzResearch.WordTrace]
  refine ⟨255622490502260395352777477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170414993668173596901851651 255622490502260395352777477)
  ·
    refine ⟨47929216969173824128645777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255622490502260395352777477 47929216969173824128645777)
    ·
      refine ⟨35946912726880368096484333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47929216969173824128645777 35946912726880368096484333)
      ·
        refine ⟨13480092272580138036181625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35946912726880368096484333 13480092272580138036181625)
        ·
          refine ⟨10110069204435103527136219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13480092272580138036181625 10110069204435103527136219)
          ·
            refine ⟨15165103806652655290704329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10110069204435103527136219 15165103806652655290704329)
            ·
              refine ⟨11373827854989491468028247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15165103806652655290704329 11373827854989491468028247)
              ·
                refine ⟨17060741782484237202042371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11373827854989491468028247 17060741782484237202042371)
                ·
                  refine ⟨25591112673726355803063557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17060741782484237202042371 25591112673726355803063557)
                  ·
                    refine ⟨4798333626323691713074417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25591112673726355803063557 4798333626323691713074417)
                    ·
                      refine ⟨3598750219742768784805813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798333626323691713074417 3598750219742768784805813)
                      ·
                        rfl

theorem cell23_7008541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_7008541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008541 prefixEnd_7008541 := by exact prefixLift 7008541
  have htrace : WordTrace (prefixWord ++ tailWord_7008541) baseStart_7008541 baseEnd_7008541 := by
    simpa [prefixWord, tailWord_7008541, baseEnd_7008541] using wordTrace_append hprefix tailTrace_7008541
  have hstable : (prefixWord ++ tailWord_7008541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008541).length < 2 ^ (prefixWord ++ tailWord_7008541).sum := by decide
  have hdescent : baseEnd_7008541 < baseStart_7008541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008560 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 2, 5]
def baseStart_7008560 : Nat := 118140960795 + 7008560 * 2 ^ 59
def prefixEnd_7008560 : Nat := 4983230072969 + 3 ^ 40 * 7008560 * 2
def baseEnd_7008560 : Nat := 1199586658625068070156075

theorem tailTrace_7008560 : CollatzResearch.WordTrace tailWord_7008560 prefixEnd_7008560 1199586658625068070156075 := by
  unfold tailWord_7008560
  simp only [CollatzResearch.WordTrace]
  refine ⟨127811591744595780798859567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170415455659461041065146089 127811591744595780798859567)
  ·
    refine ⟨191717387616893671198289351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127811591744595780798859567 191717387616893671198289351)
    ·
      refine ⟨287576081425340506797434027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191717387616893671198289351 287576081425340506797434027)
      ·
        refine ⟨431364122138010760196151041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287576081425340506797434027 431364122138010760196151041)
        ·
          refine ⟨323523091603508070147113281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431364122138010760196151041 323523091603508070147113281)
          ·
            refine ⟨242642318702631052610334961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323523091603508070147113281 242642318702631052610334961)
            ·
              refine ⟨181981739026973289457751221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242642318702631052610334961 181981739026973289457751221)
              ·
                refine ⟨17060788033778745886664177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181981739026973289457751221 17060788033778745886664177)
                ·
                  refine ⟨12795591025334059414998133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17060788033778745886664177 12795591025334059414998133)
                  ·
                    refine ⟨1199586658625068070156075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12795591025334059414998133 1199586658625068070156075)
                    ·
                      rfl

theorem cell23_7008560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_7008560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008560 prefixEnd_7008560 := by exact prefixLift 7008560
  have htrace : WordTrace (prefixWord ++ tailWord_7008560) baseStart_7008560 baseEnd_7008560 := by
    simpa [prefixWord, tailWord_7008560, baseEnd_7008560] using wordTrace_append hprefix tailTrace_7008560
  have hstable : (prefixWord ++ tailWord_7008560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008560).length < 2 ^ (prefixWord ++ tailWord_7008560).sum := by decide
  have hdescent : baseEnd_7008560 < baseStart_7008560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008564 : List Nat := [2, 5, 1, 1, 1, 2, 1, 5, 5]
def baseStart_7008564 : Nat := 118140960795 + 7008564 * 2 ^ 59
def prefixEnd_7008564 : Nat := 4983230072969 + 3 ^ 40 * 7008564 * 2
def baseEnd_7008564 : Nat := 399862447755313577202023

theorem tailTrace_7008564 : CollatzResearch.WordTrace tailWord_7008564 prefixEnd_7008564 399862447755313577202023 := by
  unfold tailWord_7008564
  simp only [CollatzResearch.WordTrace]
  refine ⟨127811664690588535140432373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170415552920784713520576497 127811664690588535140432373)
  ·
    refine ⟨11982343564742675169415535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127811664690588535140432373 11982343564742675169415535)
    ·
      refine ⟨17973515347114012754123303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11982343564742675169415535 17973515347114012754123303)
      ·
        refine ⟨26960273020671019131184955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17973515347114012754123303 26960273020671019131184955)
        ·
          refine ⟨40440409531006528696777433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26960273020671019131184955 40440409531006528696777433)
          ·
            refine ⟨30330307148254896522583075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40440409531006528696777433 30330307148254896522583075)
            ·
              refine ⟨45495460722382344783874613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30330307148254896522583075 45495460722382344783874613)
              ·
                refine ⟨4265199442723344823488245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45495460722382344783874613 4265199442723344823488245)
                ·
                  refine ⟨399862447755313577202023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265199442723344823488245 399862447755313577202023)
                  ·
                    rfl

theorem cell23_7008564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_7008564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008564 prefixEnd_7008564 := by exact prefixLift 7008564
  have htrace : WordTrace (prefixWord ++ tailWord_7008564) baseStart_7008564 baseEnd_7008564 := by
    simpa [prefixWord, tailWord_7008564, baseEnd_7008564] using wordTrace_append hprefix tailTrace_7008564
  have hstable : (prefixWord ++ tailWord_7008564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008564).length < 2 ^ (prefixWord ++ tailWord_7008564).sum := by decide
  have hdescent : baseEnd_7008564 < baseStart_7008564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008607 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 3, 4]
def baseStart_7008607 : Nat := 118140960795 + 7008607 * 2 ^ 59
def prefixEnd_7008607 : Nat := 4983230072969 + 3 ^ 40 * 7008607 * 2
def baseEnd_7008607 : Nat := 1199594703155321842193503

theorem tailTrace_7008607 : CollatzResearch.WordTrace tailWord_7008607 prefixEnd_7008607 1199594703155321842193503 := by
  unfold tailWord_7008607
  simp only [CollatzResearch.WordTrace]
  refine ⟨255624897720021288624680075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170416598480014192416453383 255624897720021288624680075)
  ·
    refine ⟨383437346580031932937020113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255624897720021288624680075 383437346580031932937020113)
    ·
      refine ⟨287578009935023949702765085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383437346580031932937020113 287578009935023949702765085)
      ·
        refine ⟨107841753725633981138536907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287578009935023949702765085 107841753725633981138536907)
        ·
          refine ⟨161762630588450971707805361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107841753725633981138536907 161762630588450971707805361)
          ·
            refine ⟨121321972941338228780854021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161762630588450971707805361 121321972941338228780854021)
            ·
              refine ⟨22747869926500917896410129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121321972941338228780854021 22747869926500917896410129)
              ·
                refine ⟨17060902444875688422307597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22747869926500917896410129 17060902444875688422307597)
                ·
                  refine ⟨6397838416828383158365349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17060902444875688422307597 6397838416828383158365349)
                  ·
                    refine ⟨1199594703155321842193503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6397838416828383158365349 1199594703155321842193503)
                    ·
                      rfl

theorem cell23_7008607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 4].length) (baseStart_7008607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008607 prefixEnd_7008607 := by exact prefixLift 7008607
  have htrace : WordTrace (prefixWord ++ tailWord_7008607) baseStart_7008607 baseEnd_7008607 := by
    simpa [prefixWord, tailWord_7008607, baseEnd_7008607] using wordTrace_append hprefix tailTrace_7008607
  have hstable : (prefixWord ++ tailWord_7008607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008607).length < 2 ^ (prefixWord ++ tailWord_7008607).sum := by decide
  have hdescent : baseEnd_7008607 < baseStart_7008607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008617 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 3]
def baseStart_7008617 : Nat := 118140960795 + 7008617 * 2 ^ 59
def prefixEnd_7008617 : Nat := 4983230072969 + 3 ^ 40 * 7008617 * 2
def baseEnd_7008617 : Nat := 3598789244272510487455463

theorem tailTrace_7008617 : CollatzResearch.WordTrace tailWord_7008617 prefixEnd_7008617 3598789244272510487455463 := by
  unfold tailWord_7008617
  simp only [CollatzResearch.WordTrace]
  refine ⟨255625262449985060332544105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170416841633323373555029403 255625262449985060332544105)
  ·
    refine ⟨191718946837488795249408079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255625262449985060332544105 191718946837488795249408079)
    ·
      refine ⟨287578420256233192874112119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191718946837488795249408079 287578420256233192874112119)
      ·
        refine ⟨431367630384349789311168179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287578420256233192874112119 431367630384349789311168179)
        ·
          refine ⟨647051445576524683966752269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431367630384349789311168179 647051445576524683966752269)
          ·
            refine ⟨242644292091196756487532101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647051445576524683966752269 242644292091196756487532101)
            ·
              refine ⟨45495804767099391841412269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242644292091196756487532101 45495804767099391841412269)
              ·
                refine ⟨17060926787662271940529601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45495804767099391841412269 17060926787662271940529601)
                ·
                  refine ⟨12795695090746703955397201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17060926787662271940529601 12795695090746703955397201)
                  ·
                    refine ⟨9596771318060027966547901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12795695090746703955397201 9596771318060027966547901)
                    ·
                      refine ⟨3598789244272510487455463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9596771318060027966547901 3598789244272510487455463)
                      ·
                        rfl

theorem cell23_7008617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_7008617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008617 prefixEnd_7008617 := by exact prefixLift 7008617
  have htrace : WordTrace (prefixWord ++ tailWord_7008617) baseStart_7008617 baseEnd_7008617 := by
    simpa [prefixWord, tailWord_7008617, baseEnd_7008617] using wordTrace_append hprefix tailTrace_7008617
  have hstable : (prefixWord ++ tailWord_7008617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008617).length < 2 ^ (prefixWord ++ tailWord_7008617).sum := by decide
  have hdescent : baseEnd_7008617 < baseStart_7008617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008641 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 3, 4]
def baseStart_7008641 : Nat := 118140960795 + 7008641 * 2 ^ 59
def prefixEnd_7008641 : Nat := 4983230072969 + 3 ^ 40 * 7008641 * 2
def baseEnd_7008641 : Nat := 1199600522602739464518451

theorem tailTrace_7008641 : CollatzResearch.WordTrace tailWord_7008641 prefixEnd_7008641 1199600522602739464518451 := by
  unfold tailWord_7008641
  simp only [CollatzResearch.WordTrace]
  refine ⟨255626137801898112431417777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170417425201265408287611851 255626137801898112431417777)
  ·
    refine ⟨191719603351423584323563333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255626137801898112431417777 191719603351423584323563333)
    ·
      refine ⟨35947425628391922060668125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191719603351423584323563333 35947425628391922060668125)
      ·
        refine ⟨13480284610646970772750547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35947425628391922060668125 13480284610646970772750547)
        ·
          refine ⟨20220426915970456159125821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13480284610646970772750547 20220426915970456159125821)
          ·
            refine ⟨7582660093488921059672183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20220426915970456159125821 7582660093488921059672183)
            ·
              refine ⟨11373990140233381589508275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7582660093488921059672183 11373990140233381589508275)
              ·
                refine ⟨17060985210350072384262413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11373990140233381589508275 17060985210350072384262413)
                ·
                  refine ⟨6397869453881277144098405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17060985210350072384262413 6397869453881277144098405)
                  ·
                    refine ⟨1199600522602739464518451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6397869453881277144098405 1199600522602739464518451)
                    ·
                      rfl

theorem cell23_7008641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_7008641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008641 prefixEnd_7008641 := by exact prefixLift 7008641
  have htrace : WordTrace (prefixWord ++ tailWord_7008641) baseStart_7008641 baseEnd_7008641 := by
    simpa [prefixWord, tailWord_7008641, baseEnd_7008641] using wordTrace_append hprefix tailTrace_7008641
  have hstable : (prefixWord ++ tailWord_7008641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008641).length < 2 ^ (prefixWord ++ tailWord_7008641).sum := by decide
  have hdescent : baseEnd_7008641 < baseStart_7008641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008654 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_7008654 : Nat := 118140960795 + 7008654 * 2 ^ 59
def prefixEnd_7008654 : Nat := 4983230072969 + 3 ^ 40 * 7008654 * 2
def baseEnd_7008654 : Nat := 399867582561858538076977

theorem tailTrace_7008654 : CollatzResearch.WordTrace tailWord_7008654 prefixEnd_7008654 399867582561858538076977 := by
  unfold tailWord_7008654
  simp only [CollatzResearch.WordTrace]
  refine ⟨31953326493856376956455127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170417741300567343767760677 31953326493856376956455127)
  ·
    refine ⟨47929989740784565434682691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31953326493856376956455127 47929989740784565434682691)
    ·
      refine ⟨71894984611176848152024037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47929989740784565434682691 71894984611176848152024037)
      ·
        refine ⟨13480309614595659028504507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71894984611176848152024037 13480309614595659028504507)
        ·
          refine ⟨20220464421893488542756761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13480309614595659028504507 20220464421893488542756761)
          ·
            refine ⟨15165348316420116407067571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20220464421893488542756761 15165348316420116407067571)
            ·
              refine ⟨22748022474630174610601357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15165348316420116407067571 22748022474630174610601357)
              ·
                refine ⟨8530508427986315478975509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22748022474630174610601357 8530508427986315478975509)
                ·
                  refine ⟨399867582561858538076977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8530508427986315478975509 399867582561858538076977)
                  ·
                    rfl

theorem cell23_7008654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_7008654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008654 prefixEnd_7008654 := by exact prefixLift 7008654
  have htrace : WordTrace (prefixWord ++ tailWord_7008654) baseStart_7008654 baseEnd_7008654 := by
    simpa [prefixWord, tailWord_7008654, baseEnd_7008654] using wordTrace_append hprefix tailTrace_7008654
  have hstable : (prefixWord ++ tailWord_7008654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008654).length < 2 ^ (prefixWord ++ tailWord_7008654).sum := by decide
  have hdescent : baseEnd_7008654 < baseStart_7008654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008714 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_7008714 : Nat := 118140960795 + 7008714 * 2 ^ 59
def prefixEnd_7008714 : Nat := 4983230072969 + 3 ^ 40 * 7008714 * 2
def baseEnd_7008714 : Nat := 1199613017298665535980839

theorem tailTrace_7008714 : CollatzResearch.WordTrace tailWord_7008714 prefixEnd_7008714 1199613017298665535980839 := by
  unfold tailWord_7008714
  simp only [CollatzResearch.WordTrace]
  refine ⟨63907200082658411474706299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170419200220422430599216797 63907200082658411474706299)
  ·
    refine ⟨95860800123987617212059449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63907200082658411474706299 95860800123987617212059449)
    ·
      refine ⟨71895600092990712909044587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95860800123987617212059449 71895600092990712909044587)
      ·
        refine ⟨107843400139486069363566881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71895600092990712909044587 107843400139486069363566881)
        ·
          refine ⟨80882550104614552022675161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107843400139486069363566881 80882550104614552022675161)
          ·
            refine ⟨60661912578460914017006371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80882550104614552022675161 60661912578460914017006371)
            ·
              refine ⟨90992868867691371025509557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60661912578460914017006371 90992868867691371025509557)
              ·
                refine ⟨8530581456346066033641521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90992868867691371025509557 8530581456346066033641521)
                ·
                  refine ⟨6397936092259549525231141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8530581456346066033641521 6397936092259549525231141)
                  ·
                    refine ⟨1199613017298665535980839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6397936092259549525231141 1199613017298665535980839)
                    ·
                      rfl

theorem cell23_7008714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_7008714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008714 prefixEnd_7008714 := by exact prefixLift 7008714
  have htrace : WordTrace (prefixWord ++ tailWord_7008714) baseStart_7008714 baseEnd_7008714 := by
    simpa [prefixWord, tailWord_7008714, baseEnd_7008714] using wordTrace_append hprefix tailTrace_7008714
  have hstable : (prefixWord ++ tailWord_7008714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008714).length < 2 ^ (prefixWord ++ tailWord_7008714).sum := by decide
  have hdescent : baseEnd_7008714 < baseStart_7008714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008788 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_7008788 : Nat := 118140960795 + 7008788 * 2 ^ 59
def prefixEnd_7008788 : Nat := 4983230072969 + 3 ^ 40 * 7008788 * 2
def baseEnd_7008788 : Nat := 3598877049464429318417177

theorem tailTrace_7008788 : CollatzResearch.WordTrace tailWord_7008788 prefixEnd_7008788 3598877049464429318417177 := by
  unfold tailWord_7008788
  simp only [CollatzResearch.WordTrace]
  refine ⟨127815749666182778268509509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170420999554910371024679345 127815749666182778268509509)
  ·
    refine ⟨23965453062409270925345533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127815749666182778268509509 23965453062409270925345533)
    ·
      refine ⟨8987044898403476597004575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23965453062409270925345533 8987044898403476597004575)
      ·
        refine ⟨13480567347605214895506863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8987044898403476597004575 13480567347605214895506863)
        ·
          refine ⟨20220851021407822343260295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13480567347605214895506863 20220851021407822343260295)
          ·
            refine ⟨30331276532111733514890443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20220851021407822343260295 30331276532111733514890443)
            ·
              refine ⟨45496914798167600272335665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30331276532111733514890443 45496914798167600272335665)
              ·
                refine ⟨34122686098625700204251749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45496914798167600272335665 34122686098625700204251749)
                ·
                  refine ⟨6398003643492318788297203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34122686098625700204251749 6398003643492318788297203)
                  ·
                    refine ⟨9597005465238478182445805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398003643492318788297203 9597005465238478182445805)
                    ·
                      refine ⟨3598877049464429318417177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9597005465238478182445805 3598877049464429318417177)
                      ·
                        rfl

theorem cell23_7008788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_7008788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008788 prefixEnd_7008788 := by exact prefixLift 7008788
  have htrace : WordTrace (prefixWord ++ tailWord_7008788) baseStart_7008788 baseEnd_7008788 := by
    simpa [prefixWord, tailWord_7008788, baseEnd_7008788] using wordTrace_append hprefix tailTrace_7008788
  have hstable : (prefixWord ++ tailWord_7008788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008788).length < 2 ^ (prefixWord ++ tailWord_7008788).sum := by decide
  have hdescent : baseEnd_7008788 < baseStart_7008788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008822 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_7008822 : Nat := 118140960795 + 7008822 * 2 ^ 59
def prefixEnd_7008822 : Nat := 4983230072969 + 3 ^ 40 * 7008822 * 2
def baseEnd_7008822 : Nat := 3598894507806682185392021

theorem tailTrace_7008822 : CollatzResearch.WordTrace tailWord_7008822 prefixEnd_7008822 3598894507806682185392021 := by
  unfold tailWord_7008822
  simp only [CollatzResearch.WordTrace]
  refine ⟨15977046213390148771484795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170421826276161586895837813 15977046213390148771484795)
  ·
    refine ⟨23965569320085223157227193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15977046213390148771484795 23965569320085223157227193)
    ·
      refine ⟨17974176990063917367920395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23965569320085223157227193 17974176990063917367920395)
      ·
        refine ⟨26961265485095876051880593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17974176990063917367920395 26961265485095876051880593)
        ·
          refine ⟨20220949113821907038910445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26961265485095876051880593 20220949113821907038910445)
          ·
            refine ⟨7582855917683215139591417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20220949113821907038910445 7582855917683215139591417)
            ·
              refine ⟨5687141938262411354693563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7582855917683215139591417 5687141938262411354693563)
              ·
                refine ⟨8530712907393617032040345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687141938262411354693563 8530712907393617032040345)
                ·
                  refine ⟨6398034680545212774030259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8530712907393617032040345 6398034680545212774030259)
                  ·
                    refine ⟨9597052020817819161045389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398034680545212774030259 9597052020817819161045389)
                    ·
                      refine ⟨3598894507806682185392021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9597052020817819161045389 3598894507806682185392021)
                      ·
                        rfl

theorem cell23_7008822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_7008822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008822 prefixEnd_7008822 := by exact prefixLift 7008822
  have htrace : WordTrace (prefixWord ++ tailWord_7008822) baseStart_7008822 baseEnd_7008822 := by
    simpa [prefixWord, tailWord_7008822, baseEnd_7008822] using wordTrace_append hprefix tailTrace_7008822
  have hstable : (prefixWord ++ tailWord_7008822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008822).length < 2 ^ (prefixWord ++ tailWord_7008822).sum := by decide
  have hdescent : baseEnd_7008822 < baseStart_7008822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008847 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 1, 7]
def baseStart_7008847 : Nat := 118140960795 + 7008847 * 2 ^ 59
def prefixEnd_7008847 : Nat := 4983230072969 + 3 ^ 40 * 7008847 * 2
def baseEnd_7008847 : Nat := 1199635781607681529193135

theorem tailTrace_7008847 : CollatzResearch.WordTrace tailWord_7008847 prefixEnd_7008847 1199635781607681529193135 := by
  unfold tailWord_7008847
  simp only [CollatzResearch.WordTrace]
  refine ⟨255633651239151809613416795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170422434159434539742277863 255633651239151809613416795)
  ·
    refine ⟨383450476858727714420125193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255633651239151809613416795 383450476858727714420125193)
    ·
      refine ⟨287587857644045785815093895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383450476858727714420125193 287587857644045785815093895)
      ·
        refine ⟨431381786466068678722640843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287587857644045785815093895 431381786466068678722640843)
        ·
          refine ⟨647072679699103018083961265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431381786466068678722640843 647072679699103018083961265)
          ·
            refine ⟨485304509774327263562970949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647072679699103018083961265 485304509774327263562970949)
            ·
              refine ⟨90994595582686361918057053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 485304509774327263562970949 90994595582686361918057053)
              ·
                refine ⟨34122973343507385719271395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90994595582686361918057053 34122973343507385719271395)
                ·
                  refine ⟨51184460015261078578907093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34122973343507385719271395 51184460015261078578907093)
                  ·
                    refine ⟨1199635781607681529193135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51184460015261078578907093 1199635781607681529193135)
                    ·
                      rfl

theorem cell23_7008847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_7008847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008847 prefixEnd_7008847 := by exact prefixLift 7008847
  have htrace : WordTrace (prefixWord ++ tailWord_7008847) baseStart_7008847 baseEnd_7008847 := by
    simpa [prefixWord, tailWord_7008847, baseEnd_7008847] using wordTrace_append hprefix tailTrace_7008847
  have hstable : (prefixWord ++ tailWord_7008847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008847).length < 2 ^ (prefixWord ++ tailWord_7008847).sum := by decide
  have hdescent : baseEnd_7008847 < baseStart_7008847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008864 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 2, 5]
def baseStart_7008864 : Nat := 118140960795 + 7008864 * 2 ^ 59
def prefixEnd_7008864 : Nat := 4983230072969 + 3 ^ 40 * 7008864 * 2
def baseEnd_7008864 : Nat := 1199638691331390340355609

theorem tailTrace_7008864 : CollatzResearch.WordTrace tailWord_7008864 prefixEnd_7008864 1199638691331390340355609 := by
  unfold tailWord_7008864
  simp only [CollatzResearch.WordTrace]
  refine ⟨127817135640045110758392823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170422847520060147677857097 127817135640045110758392823)
  ·
    refine ⟨191725703460067666137589235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127817135640045110758392823 191725703460067666137589235)
    ·
      refine ⟨287588555190101499206383853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191725703460067666137589235 287588555190101499206383853)
      ·
        refine ⟨107845708196288062202393945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287588555190101499206383853 107845708196288062202393945)
        ·
          refine ⟨80884281147216046651795459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107845708196288062202393945 80884281147216046651795459)
          ·
            refine ⟨121326421720824069977693189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80884281147216046651795459 121326421720824069977693189)
            ·
              refine ⟨22748704072654513120817473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121326421720824069977693189 22748704072654513120817473)
              ·
                refine ⟨17061528054490884840613105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22748704072654513120817473 17061528054490884840613105)
                ·
                  refine ⟨12796146040868163630459829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17061528054490884840613105 12796146040868163630459829)
                  ·
                    refine ⟨1199638691331390340355609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12796146040868163630459829 1199638691331390340355609)
                    ·
                      rfl

theorem cell23_7008864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_7008864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008864 prefixEnd_7008864 := by exact prefixLift 7008864
  have htrace : WordTrace (prefixWord ++ tailWord_7008864) baseStart_7008864 baseEnd_7008864 := by
    simpa [prefixWord, tailWord_7008864, baseEnd_7008864] using wordTrace_append hprefix tailTrace_7008864
  have hstable : (prefixWord ++ tailWord_7008864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008864).length < 2 ^ (prefixWord ++ tailWord_7008864).sum := by decide
  have hdescent : baseEnd_7008864 < baseStart_7008864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008874 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7008874 : Nat := 118140960795 + 7008874 * 2 ^ 59
def prefixEnd_7008874 : Nat := 4983230072969 + 3 ^ 40 * 7008874 * 2
def baseEnd_7008874 : Nat := 3598921208800715981941781

theorem tailTrace_7008874 : CollatzResearch.WordTrace tailWord_7008874 prefixEnd_7008874 3598921208800715981941781 := by
  unfold tailWord_7008874
  simp only [CollatzResearch.WordTrace]
  refine ⟨63908659002513498306162419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170423090673369328816433117 63908659002513498306162419)
  ·
    refine ⟨95862988503770247459243629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63908659002513498306162419 95862988503770247459243629)
    ·
      refine ⟨35948620688913842797216361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95862988503770247459243629 35948620688913842797216361)
      ·
        refine ⟨26961465516685382097912271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35948620688913842797216361 26961465516685382097912271)
        ·
          refine ⟨40442198275028073146868407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26961465516685382097912271 40442198275028073146868407)
          ·
            refine ⟨60663297412542109720302611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40442198275028073146868407 60663297412542109720302611)
            ·
              refine ⟨90994946118813164580453917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60663297412542109720302611 90994946118813164580453917)
              ·
                refine ⟨34123104794554936717670219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90994946118813164580453917 34123104794554936717670219)
                ·
                  refine ⟨51184657191832405076505329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34123104794554936717670219 51184657191832405076505329)
                  ·
                    refine ⟨38388492893874303807378997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51184657191832405076505329 38388492893874303807378997)
                    ·
                      refine ⟨3598921208800715981941781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38388492893874303807378997 3598921208800715981941781)
                      ·
                        rfl

theorem cell23_7008874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7008874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008874 prefixEnd_7008874 := by exact prefixLift 7008874
  have htrace : WordTrace (prefixWord ++ tailWord_7008874) baseStart_7008874 baseEnd_7008874 := by
    simpa [prefixWord, tailWord_7008874, baseEnd_7008874] using wordTrace_append hprefix tailTrace_7008874
  have hstable : (prefixWord ++ tailWord_7008874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008874).length < 2 ^ (prefixWord ++ tailWord_7008874).sum := by decide
  have hdescent : baseEnd_7008874 < baseStart_7008874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008901 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_7008901 : Nat := 118140960795 + 7008901 * 2 ^ 59
def prefixEnd_7008901 : Nat := 4983230072969 + 3 ^ 40 * 7008901 * 2
def baseEnd_7008901 : Nat := 3598935072778387376304157

theorem tailTrace_7008901 : CollatzResearch.WordTrace tailWord_7008901 prefixEnd_7008901 3598935072778387376304157 := by
  unfold tailWord_7008901
  simp only [CollatzResearch.WordTrace]
  refine ⟨255635620780956176835882557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170423747187304117890588371 255635620780956176835882557)
  ·
    refine ⟨95863357792858566313455959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255635620780956176835882557 95863357792858566313455959)
    ·
      refine ⟨143795036689287849470183939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95863357792858566313455959 143795036689287849470183939)
      ·
        refine ⟨215692555033931774205275909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143795036689287849470183939 215692555033931774205275909)
        ·
          refine ⟨40442354068862207663489233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215692555033931774205275909 40442354068862207663489233)
          ·
            refine ⟨30331765551646655747616925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40442354068862207663489233 30331765551646655747616925)
            ·
              refine ⟨11374412081867495905356347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30331765551646655747616925 11374412081867495905356347)
              ·
                refine ⟨17061618122801243858034521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11374412081867495905356347 17061618122801243858034521)
                ·
                  refine ⟨12796213592100932893525891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17061618122801243858034521 12796213592100932893525891)
                  ·
                    refine ⟨19194320388151399340288837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12796213592100932893525891 19194320388151399340288837)
                    ·
                      refine ⟨3598935072778387376304157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19194320388151399340288837 3598935072778387376304157)
                      ·
                        rfl

theorem cell23_7008901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_7008901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008901 prefixEnd_7008901 := by exact prefixLift 7008901
  have htrace : WordTrace (prefixWord ++ tailWord_7008901) baseStart_7008901 baseEnd_7008901 := by
    simpa [prefixWord, tailWord_7008901, baseEnd_7008901] using wordTrace_append hprefix tailTrace_7008901
  have hstable : (prefixWord ++ tailWord_7008901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008901).length < 2 ^ (prefixWord ++ tailWord_7008901).sum := by decide
  have hdescent : baseEnd_7008901 < baseStart_7008901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7008928 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 3, 4]
def baseStart_7008928 : Nat := 118140960795 + 7008928 * 2 ^ 59
def prefixEnd_7008928 : Nat := 4983230072969 + 3 ^ 40 * 7008928 * 2
def baseEnd_7008928 : Nat := 1199649645585352923555511

theorem tailTrace_7008928 : CollatzResearch.WordTrace tailWord_7008928 prefixEnd_7008928 1199649645585352923555511 := by
  unfold tailWord_7008928
  simp only [CollatzResearch.WordTrace]
  refine ⟨127818302775929180223557719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170424403701238906964743625 127818302775929180223557719)
  ·
    refine ⟨191727454163893770335336579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127818302775929180223557719 191727454163893770335336579)
    ·
      refine ⟨287591181245840655503004869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191727454163893770335336579 287591181245840655503004869)
      ·
        refine ⟨53923346483595122906813413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287591181245840655503004869 53923346483595122906813413)
        ·
          refine ⟨10110627465674085545027515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53923346483595122906813413 10110627465674085545027515)
          ·
            refine ⟨15165941198511128317541273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10110627465674085545027515 15165941198511128317541273)
            ·
              refine ⟨11374455898883346238155955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15165941198511128317541273 11374455898883346238155955)
              ·
                refine ⟨17061683848325019357233933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11374455898883346238155955 17061683848325019357233933)
                ·
                  refine ⟨6398131443121882258962725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17061683848325019357233933 6398131443121882258962725)
                  ·
                    refine ⟨1199649645585352923555511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6398131443121882258962725 1199649645585352923555511)
                    ·
                      rfl

theorem cell23_7008928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 4].length) (baseStart_7008928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7008928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7008928 prefixEnd_7008928 := by exact prefixLift 7008928
  have htrace : WordTrace (prefixWord ++ tailWord_7008928) baseStart_7008928 baseEnd_7008928 := by
    simpa [prefixWord, tailWord_7008928, baseEnd_7008928] using wordTrace_append hprefix tailTrace_7008928
  have hstable : (prefixWord ++ tailWord_7008928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7008928).length < 2 ^ (prefixWord ++ tailWord_7008928).sum := by decide
  have hdescent : baseEnd_7008928 < baseStart_7008928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7008928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
