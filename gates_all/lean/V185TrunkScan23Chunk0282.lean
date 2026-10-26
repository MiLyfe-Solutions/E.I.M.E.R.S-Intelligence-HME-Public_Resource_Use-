import V185TrunkScan23Chunk0281

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1667069 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_1667069 : Nat := 118140960795 + 1667069 * 2 ^ 59
def prefixEnd_1667069 : Nat := 4983230072969 + 3 ^ 40 * 1667069 * 2
def baseEnd_1667069 : Nat := 856007681210243318570795

theorem tailTrace_1667069 : CollatzResearch.WordTrace tailWord_1667069 prefixEnd_1667069 856007681210243318570795 := by
  unfold tailWord_1667069
  simp only [CollatzResearch.WordTrace]
  refine ⟨60803001597501200563172261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40535334398334133708781507 60803001597501200563172261)
  ·
    refine ⟨11400562799531475105594799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60803001597501200563172261 11400562799531475105594799)
    ·
      refine ⟨17100844199297212658392199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11400562799531475105594799 17100844199297212658392199)
      ·
        refine ⟨25651266298945818987588299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17100844199297212658392199 25651266298945818987588299)
        ·
          refine ⟨38476899448418728481382449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25651266298945818987588299 38476899448418728481382449)
          ·
            refine ⟨28857674586314046361036837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38476899448418728481382449 28857674586314046361036837)
            ·
              refine ⟨5410813984933883692694407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28857674586314046361036837 5410813984933883692694407)
              ·
                refine ⟨8116220977400825539041611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5410813984933883692694407 8116220977400825539041611)
                ·
                  refine ⟨12174331466101238308562417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8116220977400825539041611 12174331466101238308562417)
                  ·
                    refine ⟨9130748599575928731421813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12174331466101238308562417 9130748599575928731421813)
                    ·
                      refine ⟨856007681210243318570795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9130748599575928731421813 856007681210243318570795)
                      ·
                        rfl

theorem cell23_1667069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_1667069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667069 prefixEnd_1667069 := by exact prefixLift 1667069
  have htrace : WordTrace (prefixWord ++ tailWord_1667069) baseStart_1667069 baseEnd_1667069 := by
    simpa [prefixWord, tailWord_1667069, baseEnd_1667069] using wordTrace_append hprefix tailTrace_1667069
  have hstable : (prefixWord ++ tailWord_1667069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667069).length < 2 ^ (prefixWord ++ tailWord_1667069).sum := by decide
  have hdescent : baseEnd_1667069 < baseStart_1667069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667093 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_1667093 : Nat := 118140960795 + 1667093 * 2 ^ 59
def prefixEnd_1667093 : Nat := 4983230072969 + 3 ^ 40 * 1667093 * 2
def baseEnd_1667093 : Nat := 285340001581983741556895

theorem tailTrace_1667093 : CollatzResearch.WordTrace tailWord_1667093 prefixEnd_1667093 285340001581983741556895 := by
  unfold tailWord_1667093
  simp only [CollatzResearch.WordTrace]
  refine ⟨60803876949414252662045933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40535917966276168441363955 60803876949414252662045933)
  ·
    refine ⟨22801453856030344748267225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60803876949414252662045933 22801453856030344748267225)
    ·
      refine ⟨17101090392022758561200419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22801453856030344748267225 17101090392022758561200419)
      ·
        refine ⟨25651635588034137841800629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17101090392022758561200419 25651635588034137841800629)
        ·
          refine ⟨2404840836378200422668809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25651635588034137841800629 2404840836378200422668809)
          ·
            refine ⟨1803630627283650317001607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2404840836378200422668809 1803630627283650317001607)
            ·
              refine ⟨2705445940925475475502411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803630627283650317001607 2705445940925475475502411)
              ·
                refine ⟨4058168911388213213253617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705445940925475475502411 4058168911388213213253617)
                ·
                  refine ⟨3043626683541159909940213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4058168911388213213253617 3043626683541159909940213)
                  ·
                    refine ⟨285340001581983741556895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3043626683541159909940213 285340001581983741556895)
                    ·
                      rfl

theorem cell23_1667093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_1667093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667093 prefixEnd_1667093 := by exact prefixLift 1667093
  have htrace : WordTrace (prefixWord ++ tailWord_1667093) baseStart_1667093 baseEnd_1667093 := by
    simpa [prefixWord, tailWord_1667093, baseEnd_1667093] using wordTrace_append hprefix tailTrace_1667093
  have hstable : (prefixWord ++ tailWord_1667093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667093).length < 2 ^ (prefixWord ++ tailWord_1667093).sum := by decide
  have hdescent : baseEnd_1667093 < baseStart_1667093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667096 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 1, 6, 2]
def baseStart_1667096 : Nat := 118140960795 + 1667096 * 2 ^ 59
def prefixEnd_1667096 : Nat := 4983230072969 + 3 ^ 40 * 1667096 * 2
def baseEnd_1667096 : Nat := 856021545187914712933171

theorem tailTrace_1667096 : CollatzResearch.WordTrace tailWord_1667096 prefixEnd_1667096 856021545187914712933171 := by
  unfold tailWord_1667096
  simp only [CollatzResearch.WordTrace]
  refine ⟨30401993184201692087202571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40535990912268922782936761 30401993184201692087202571)
  ·
    refine ⟨45602989776302538130803857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30401993184201692087202571 45602989776302538130803857)
    ·
      refine ⟨34202242332226903598102893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45602989776302538130803857 34202242332226903598102893)
      ·
        refine ⟨12825840874585088849288585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34202242332226903598102893 12825840874585088849288585)
        ·
          refine ⟨9619380655938816636966439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12825840874585088849288585 9619380655938816636966439)
          ·
            refine ⟨14429070983908224955449659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9619380655938816636966439 14429070983908224955449659)
            ·
              refine ⟨21643606475862337433174489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14429070983908224955449659 21643606475862337433174489)
              ·
                refine ⟨16232704856896753074880867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21643606475862337433174489 16232704856896753074880867)
                ·
                  refine ⟨24349057285345129612321301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16232704856896753074880867 24349057285345129612321301)
                  ·
                    refine ⟨1141362060250552950577561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24349057285345129612321301 1141362060250552950577561)
                    ·
                      refine ⟨856021545187914712933171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1141362060250552950577561 856021545187914712933171)
                      ·
                        rfl

theorem cell23_1667096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_1667096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667096 prefixEnd_1667096 := by exact prefixLift 1667096
  have htrace : WordTrace (prefixWord ++ tailWord_1667096) baseStart_1667096 baseEnd_1667096 := by
    simpa [prefixWord, tailWord_1667096, baseEnd_1667096] using wordTrace_append hprefix tailTrace_1667096
  have hstable : (prefixWord ++ tailWord_1667096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667096).length < 2 ^ (prefixWord ++ tailWord_1667096).sum := by decide
  have hdescent : baseEnd_1667096 < baseStart_1667096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667106 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1667106 : Nat := 118140960795 + 1667106 * 2 ^ 59
def prefixEnd_1667106 : Nat := 4983230072969 + 3 ^ 40 * 1667106 * 2
def baseEnd_1667106 : Nat := 285342226664819891269375

theorem tailTrace_1667106 : CollatzResearch.WordTrace tailWord_1667106 prefixEnd_1667106 285342226664819891269375 := by
  unfold tailWord_1667106
  simp only [CollatzResearch.WordTrace]
  refine ⟨15201087774591788970567293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40536234065578103921512781 15201087774591788970567293)
  ·
    refine ⟨5700407915471920863962735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15201087774591788970567293 5700407915471920863962735)
    ·
      refine ⟨8550611873207881295944103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5700407915471920863962735 8550611873207881295944103)
      ·
        refine ⟨12825917809811821943916155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8550611873207881295944103 12825917809811821943916155)
        ·
          refine ⟨19238876714717732915874233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12825917809811821943916155 19238876714717732915874233)
          ·
            refine ⟨14429157536038299686905675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19238876714717732915874233 14429157536038299686905675)
            ·
              refine ⟨21643736304057449530358513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14429157536038299686905675 21643736304057449530358513)
              ·
                refine ⟨16232802228043087147768885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21643736304057449530358513 16232802228043087147768885)
                ·
                  refine ⟨1521825208879039420103333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16232802228043087147768885 1521825208879039420103333)
                  ·
                    refine ⟨285342226664819891269375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1521825208879039420103333 285342226664819891269375)
                    ·
                      rfl

theorem cell23_1667106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1667106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667106 prefixEnd_1667106 := by exact prefixLift 1667106
  have htrace : WordTrace (prefixWord ++ tailWord_1667106) baseStart_1667106 baseEnd_1667106 := by
    simpa [prefixWord, tailWord_1667106, baseEnd_1667106] using wordTrace_append hprefix tailTrace_1667106
  have hstable : (prefixWord ++ tailWord_1667106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667106).length < 2 ^ (prefixWord ++ tailWord_1667106).sum := by decide
  have hdescent : baseEnd_1667106 < baseStart_1667106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667109 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_1667109 : Nat := 118140960795 + 1667109 * 2 ^ 59
def prefixEnd_1667109 : Nat := 4983230072969 + 3 ^ 40 * 1667109 * 2
def baseEnd_1667109 : Nat := 856028220436423162070611

theorem tailTrace_1667109 : CollatzResearch.WordTrace tailWord_1667109 prefixEnd_1667109 856028220436423162070611 := by
  unfold tailWord_1667109
  simp only [CollatzResearch.WordTrace]
  refine ⟨60804460517356287394628381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40536307011570858263085587 60804460517356287394628381)
  ·
    refine ⟨22801672694008607772985643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60804460517356287394628381 22801672694008607772985643)
    ·
      refine ⟨34202509041012911659478465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22801672694008607772985643 34202509041012911659478465)
      ·
        refine ⟨25651881780759683744608849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34202509041012911659478465 25651881780759683744608849)
        ·
          refine ⟨19238911335569762808456637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25651881780759683744608849 19238911335569762808456637)
          ·
            refine ⟨7214591750838661053171239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19238911335569762808456637 7214591750838661053171239)
            ·
              refine ⟨10821887626257991579756859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7214591750838661053171239 10821887626257991579756859)
              ·
                refine ⟨16232831439386987369635289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10821887626257991579756859 16232831439386987369635289)
                ·
                  refine ⟨12174623579540240527226467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16232831439386987369635289 12174623579540240527226467)
                  ·
                    refine ⟨18261935369310360790839701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12174623579540240527226467 18261935369310360790839701)
                    ·
                      refine ⟨856028220436423162070611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18261935369310360790839701 856028220436423162070611)
                      ·
                        rfl

theorem cell23_1667109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_1667109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667109 prefixEnd_1667109 := by exact prefixLift 1667109
  have htrace : WordTrace (prefixWord ++ tailWord_1667109) baseStart_1667109 baseEnd_1667109 := by
    simpa [prefixWord, tailWord_1667109, baseEnd_1667109] using wordTrace_append hprefix tailTrace_1667109
  have hstable : (prefixWord ++ tailWord_1667109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667109).length < 2 ^ (prefixWord ++ tailWord_1667109).sum := by decide
  have hdescent : baseEnd_1667109 < baseStart_1667109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667119 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 6]
def baseStart_1667119 : Nat := 118140960795 + 1667119 * 2 ^ 59
def prefixEnd_1667119 : Nat := 4983230072969 + 3 ^ 40 * 1667119 * 2
def baseEnd_1667119 : Nat := 95114817249218680327285

theorem tailTrace_1667119 : CollatzResearch.WordTrace tailWord_1667119 prefixEnd_1667119 95114817249218680327285 := by
  unfold tailWord_1667119
  simp only [CollatzResearch.WordTrace]
  refine ⟨60804825247320059102492411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40536550164880039401661607 60804825247320059102492411)
  ·
    refine ⟨91207237870980088653738617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60804825247320059102492411 91207237870980088653738617)
    ·
      refine ⟨68405428403235066490303963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91207237870980088653738617 68405428403235066490303963)
      ·
        refine ⟨102608142604852599735455945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68405428403235066490303963 102608142604852599735455945)
        ·
          refine ⟨76956106953639449801591959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102608142604852599735455945 76956106953639449801591959)
          ·
            refine ⟨115434160430459174702387939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76956106953639449801591959 115434160430459174702387939)
            ·
              refine ⟨173151240645688762053581909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115434160430459174702387939 173151240645688762053581909)
              ·
                refine ⟨2029116101316665180315413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 173151240645688762053581909 2029116101316665180315413)
                ·
                  refine ⟨95114817249218680327285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2029116101316665180315413 95114817249218680327285)
                  ·
                    rfl

theorem cell23_1667119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 6].length) (baseStart_1667119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667119 prefixEnd_1667119 := by exact prefixLift 1667119
  have htrace : WordTrace (prefixWord ++ tailWord_1667119) baseStart_1667119 baseEnd_1667119 := by
    simpa [prefixWord, tailWord_1667119, baseEnd_1667119] using wordTrace_append hprefix tailTrace_1667119
  have hstable : (prefixWord ++ tailWord_1667119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667119).length < 2 ^ (prefixWord ++ tailWord_1667119).sum := by decide
  have hdescent : baseEnd_1667119 < baseStart_1667119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667123 : List Nat := [1, 1, 1, 2, 4, 1, 4, 4, 1, 4]
def baseStart_1667123 : Nat := 118140960795 + 1667123 * 2 ^ 59
def prefixEnd_1667123 : Nat := 4983230072969 + 3 ^ 40 * 1667123 * 2
def baseEnd_1667123 : Nat := 285345136388528702431849

theorem tailTrace_1667123 : CollatzResearch.WordTrace tailWord_1667123 prefixEnd_1667123 285345136388528702431849 := by
  unfold tailWord_1667123
  simp only [CollatzResearch.WordTrace]
  refine ⟨60804971139305567785638023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40536647426203711857092015 60804971139305567785638023)
  ·
    refine ⟨91207456708958351678457035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60804971139305567785638023 91207456708958351678457035)
    ·
      refine ⟨136811185063437527517685553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91207456708958351678457035 136811185063437527517685553)
      ·
        refine ⟨102608388797578145638264165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136811185063437527517685553 102608388797578145638264165)
        ·
          refine ⟨19239072899545902307174531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102608388797578145638264165 19239072899545902307174531)
          ·
            refine ⟨28858609349318853460761797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19239072899545902307174531 28858609349318853460761797)
            ·
              refine ⟨5410989252997285023892837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28858609349318853460761797 5410989252997285023892837)
              ·
                refine ⟨1014560484936990941979907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5410989252997285023892837 1014560484936990941979907)
                ·
                  refine ⟨1521840727405486412969861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014560484936990941979907 1521840727405486412969861)
                  ·
                    refine ⟨285345136388528702431849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1521840727405486412969861 285345136388528702431849)
                    ·
                      rfl

theorem cell23_1667123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 4].length) (baseStart_1667123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667123 prefixEnd_1667123 := by exact prefixLift 1667123
  have htrace : WordTrace (prefixWord ++ tailWord_1667123) baseStart_1667123 baseEnd_1667123 := by
    simpa [prefixWord, tailWord_1667123, baseEnd_1667123] using wordTrace_append hprefix tailTrace_1667123
  have hstable : (prefixWord ++ tailWord_1667123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667123).length < 2 ^ (prefixWord ++ tailWord_1667123).sum := by decide
  have hdescent : baseEnd_1667123 < baseStart_1667123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667126 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1667126 : Nat := 118140960795 + 1667126 * 2 ^ 59
def prefixEnd_1667126 : Nat := 4983230072969 + 3 ^ 40 * 1667126 * 2
def baseEnd_1667126 : Nat := 856036949607549595558033

theorem tailTrace_1667126 : CollatzResearch.WordTrace tailWord_1667126 prefixEnd_1667126 856036949607549595558033 := by
  unfold tailWord_1667126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3800317534893418706124827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40536720372196466198664821 3800317534893418706124827)
  ·
    refine ⟨5700476302340128059187241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3800317534893418706124827 5700476302340128059187241)
    ·
      refine ⟨4275357226755096044390431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5700476302340128059187241 4275357226755096044390431)
      ·
        refine ⟨6413035840132644066585647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275357226755096044390431 6413035840132644066585647)
        ·
          refine ⟨9619553760198966099878471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413035840132644066585647 9619553760198966099878471)
          ·
            refine ⟨14429330640298449149817707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9619553760198966099878471 14429330640298449149817707)
            ·
              refine ⟨21643995960447673724726561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14429330640298449149817707 21643995960447673724726561)
              ·
                refine ⟨16232996970335755293544921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21643995960447673724726561 16232996970335755293544921)
                ·
                  refine ⟨12174747727751816470158691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16232996970335755293544921 12174747727751816470158691)
                  ·
                    refine ⟨18262121591627724705238037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12174747727751816470158691 18262121591627724705238037)
                    ·
                      refine ⟨856036949607549595558033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18262121591627724705238037 856036949607549595558033)
                      ·
                        rfl

theorem cell23_1667126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1667126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667126 prefixEnd_1667126 := by exact prefixLift 1667126
  have htrace : WordTrace (prefixWord ++ tailWord_1667126) baseStart_1667126 baseEnd_1667126 := by
    simpa [prefixWord, tailWord_1667126, baseEnd_1667126] using wordTrace_append hprefix tailTrace_1667126
  have hstable : (prefixWord ++ tailWord_1667126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667126).length < 2 ^ (prefixWord ++ tailWord_1667126).sum := by decide
  have hdescent : baseEnd_1667126 < baseStart_1667126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667173 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 4, 3, 2]
def baseStart_1667173 : Nat := 118140960795 + 1667173 * 2 ^ 59
def prefixEnd_1667173 : Nat := 4983230072969 + 3 ^ 40 * 1667173 * 2
def baseEnd_1667173 : Nat := 856061083198310911670317

theorem tailTrace_1667173 : CollatzResearch.WordTrace tailWord_1667173 prefixEnd_1667173 856061083198310911670317 := by
  unfold tailWord_1667173
  simp only [CollatzResearch.WordTrace]
  refine ⟨60806794789124426324958173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40537863192749617549972115 60806794789124426324958173)
  ·
    refine ⟨22802548045921659871859315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60806794789124426324958173 22802548045921659871859315)
    ·
      refine ⟨34203822068882489807788973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22802548045921659871859315 34203822068882489807788973)
      ·
        refine ⟨12826433275830933677920865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34203822068882489807788973 12826433275830933677920865)
        ·
          refine ⟨9619824956873200258440649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12826433275830933677920865 9619824956873200258440649)
          ·
            refine ⟨7214868717654900193830487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9619824956873200258440649 7214868717654900193830487)
            ·
              refine ⟨10822303076482350290745731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7214868717654900193830487 10822303076482350290745731)
              ·
                refine ⟨16233454614723525436118597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10822303076482350290745731 16233454614723525436118597)
                ·
                  refine ⟨3043772740260661019272237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16233454614723525436118597 3043772740260661019272237)
                  ·
                    refine ⟨1141414777597747882227089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043772740260661019272237 1141414777597747882227089)
                    ·
                      refine ⟨856061083198310911670317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1141414777597747882227089 856061083198310911670317)
                      ·
                        rfl

theorem cell23_1667173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_1667173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667173 prefixEnd_1667173 := by exact prefixLift 1667173
  have htrace : WordTrace (prefixWord ++ tailWord_1667173) baseStart_1667173 baseEnd_1667173 := by
    simpa [prefixWord, tailWord_1667173, baseEnd_1667173] using wordTrace_append hprefix tailTrace_1667173
  have hstable : (prefixWord ++ tailWord_1667173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667173).length < 2 ^ (prefixWord ++ tailWord_1667173).sum := by decide
  have hdescent : baseEnd_1667173 < baseStart_1667173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667180 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 3]
def baseStart_1667180 : Nat := 118140960795 + 1667180 * 2 ^ 59
def prefixEnd_1667180 : Nat := 4983230072969 + 3 ^ 40 * 1667180 * 2
def baseEnd_1667180 : Nat := 856064677562892384282785

theorem tailTrace_1667180 : CollatzResearch.WordTrace tailWord_1667180 prefixEnd_1667180 856064677562892384282785 := by
  unfold tailWord_1667180
  simp only [CollatzResearch.WordTrace]
  refine ⟨30403525050049533260231497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40538033400066044346975329 30403525050049533260231497)
  ·
    refine ⟨22802643787537149945173623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30403525050049533260231497 22802643787537149945173623)
    ·
      refine ⟨34203965681305724917760435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22802643787537149945173623 34203965681305724917760435)
      ·
        refine ⟨51305948521958587376640653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34203965681305724917760435 51305948521958587376640653)
        ·
          refine ⟨19239730695734470266240245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51305948521958587376640653 19239730695734470266240245)
          ·
            refine ⟨1803724752725106587460023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19239730695734470266240245 1803724752725106587460023)
            ·
              refine ⟨2705587129087659881190035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803724752725106587460023 2705587129087659881190035)
              ·
                refine ⟨4058380693631489821785053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705587129087659881190035 4058380693631489821785053)
                ·
                  refine ⟨1521892760111808683169395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4058380693631489821785053 1521892760111808683169395)
                  ·
                    refine ⟨2282839140167713024754093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1521892760111808683169395 2282839140167713024754093)
                    ·
                      refine ⟨856064677562892384282785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2282839140167713024754093 856064677562892384282785)
                      ·
                        rfl

theorem cell23_1667180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_1667180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667180 prefixEnd_1667180 := by exact prefixLift 1667180
  have htrace : WordTrace (prefixWord ++ tailWord_1667180) baseStart_1667180 baseEnd_1667180 := by
    simpa [prefixWord, tailWord_1667180, baseEnd_1667180] using wordTrace_append hprefix tailTrace_1667180
  have hstable : (prefixWord ++ tailWord_1667180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667180).length < 2 ^ (prefixWord ++ tailWord_1667180).sum := by decide
  have hdescent : baseEnd_1667180 < baseStart_1667180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667203 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 4]
def baseStart_1667203 : Nat := 118140960795 + 1667203 * 2 ^ 59
def prefixEnd_1667203 : Nat := 4983230072969 + 3 ^ 40 * 1667203 * 2
def baseEnd_1667203 : Nat := 856076487617945794295179

theorem tailTrace_1667203 : CollatzResearch.WordTrace tailWord_1667203 prefixEnd_1667203 856076487617945794295179 := by
  unfold tailWord_1667203
  simp only [CollatzResearch.WordTrace]
  refine ⟨60807888979015741448550263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40538592652677160965700175 60807888979015741448550263)
  ·
    refine ⟨91211833468523612172825395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60807888979015741448550263 91211833468523612172825395)
    ·
      refine ⟨136817750202785418259238093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91211833468523612172825395 136817750202785418259238093)
      ·
        refine ⟨51306656326044531847214285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136817750202785418259238093 51306656326044531847214285)
        ·
          refine ⟨19239996122266699442705357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51306656326044531847214285 19239996122266699442705357)
          ·
            refine ⟨7214998545850012291014509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19239996122266699442705357 7214998545850012291014509)
            ·
              refine ⟨2705624454693754609130441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7214998545850012291014509 2705624454693754609130441)
              ·
                refine ⟨2029218341020315956847831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705624454693754609130441 2029218341020315956847831)
                ·
                  refine ⟨3043827511530473935271747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029218341020315956847831 3043827511530473935271747)
                  ·
                    refine ⟨4565741267295710902907621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3043827511530473935271747 4565741267295710902907621)
                    ·
                      refine ⟨856076487617945794295179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4565741267295710902907621 856076487617945794295179)
                      ·
                        rfl

theorem cell23_1667203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_1667203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667203 prefixEnd_1667203 := by exact prefixLift 1667203
  have htrace : WordTrace (prefixWord ++ tailWord_1667203) baseStart_1667203 baseEnd_1667203 := by
    simpa [prefixWord, tailWord_1667203, baseEnd_1667203] using wordTrace_append hprefix tailTrace_1667203
  have hstable : (prefixWord ++ tailWord_1667203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667203).length < 2 ^ (prefixWord ++ tailWord_1667203).sum := by decide
  have hdescent : baseEnd_1667203 < baseStart_1667203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667209 : List Nat := [1, 2, 1, 1, 4, 2, 1, 11]
def baseStart_1667209 : Nat := 118140960795 + 1667209 * 2 ^ 59
def prefixEnd_1667209 : Nat := 4983230072969 + 3 ^ 40 * 1667209 * 2
def baseEnd_1667209 : Nat := 31706650685254547067413

theorem tailTrace_1667209 : CollatzResearch.WordTrace tailWord_1667209 prefixEnd_1667209 31706650685254547067413 := by
  unfold tailWord_1667209
  simp only [CollatzResearch.WordTrace]
  refine ⟨60808107816994004473268681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40538738544662669648845787 60808107816994004473268681)
  ·
    refine ⟨45606080862745503354951511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60808107816994004473268681 45606080862745503354951511)
    ·
      refine ⟨68409121294118255032427267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45606080862745503354951511 68409121294118255032427267)
      ·
        refine ⟨102613681941177382548640901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68409121294118255032427267 102613681941177382548640901)
        ·
          refine ⟨19240065363970759227870169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102613681941177382548640901 19240065363970759227870169)
          ·
            refine ⟨14430049022978069420902627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19240065363970759227870169 14430049022978069420902627)
            ·
              refine ⟨21645073534467104131353941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14430049022978069420902627 21645073534467104131353941)
              ·
                refine ⟨31706650685254547067413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21645073534467104131353941 31706650685254547067413)
                ·
                  rfl

theorem cell23_1667209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 11].length) (baseStart_1667209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667209 prefixEnd_1667209 := by exact prefixLift 1667209
  have htrace : WordTrace (prefixWord ++ tailWord_1667209) baseStart_1667209 baseEnd_1667209 := by
    simpa [prefixWord, tailWord_1667209, baseEnd_1667209] using wordTrace_append hprefix tailTrace_1667209
  have hstable : (prefixWord ++ tailWord_1667209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667209).length < 2 ^ (prefixWord ++ tailWord_1667209).sum := by decide
  have hdescent : baseEnd_1667209 < baseStart_1667209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667216 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_1667216 : Nat := 118140960795 + 1667216 * 2 ^ 59
def prefixEnd_1667216 : Nat := 4983230072969 + 3 ^ 40 * 1667216 * 2
def baseEnd_1667216 : Nat := 856083162866454243432619

theorem tailTrace_1667216 : CollatzResearch.WordTrace tailWord_1667216 prefixEnd_1667216 856083162866454243432619 := by
  unfold tailWord_1667216
  simp only [CollatzResearch.WordTrace]
  refine ⟨30404181563984322334386751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40538908751979096445849001 30404181563984322334386751)
  ·
    refine ⟨45606272345976483501580127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30404181563984322334386751 45606272345976483501580127)
    ·
      refine ⟨68409408518964725252370191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45606272345976483501580127 68409408518964725252370191)
      ·
        refine ⟨102614112778447087878555287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68409408518964725252370191 102614112778447087878555287)
        ·
          refine ⟨153921169167670631817832931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102614112778447087878555287 153921169167670631817832931)
          ·
            refine ⟨230881753751505947726749397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153921169167670631817832931 230881753751505947726749397)
            ·
              refine ⟨5411291103550920649845689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 230881753751505947726749397 5411291103550920649845689)
              ·
                refine ⟨4058468327663190487384267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5411291103550920649845689 4058468327663190487384267)
                ·
                  refine ⟨6087702491494785731076401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4058468327663190487384267 6087702491494785731076401)
                  ·
                    refine ⟨4565776868621089298307301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6087702491494785731076401 4565776868621089298307301)
                    ·
                      refine ⟨856083162866454243432619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4565776868621089298307301 856083162866454243432619)
                      ·
                        rfl

theorem cell23_1667216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_1667216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667216 prefixEnd_1667216 := by exact prefixLift 1667216
  have htrace : WordTrace (prefixWord ++ tailWord_1667216) baseStart_1667216 baseEnd_1667216 := by
    simpa [prefixWord, tailWord_1667216, baseEnd_1667216] using wordTrace_append hprefix tailTrace_1667216
  have hstable : (prefixWord ++ tailWord_1667216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667216).length < 2 ^ (prefixWord ++ tailWord_1667216).sum := by decide
  have hdescent : baseEnd_1667216 < baseStart_1667216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667226 : List Nat := [3, 1, 1, 5, 2, 11]
def baseStart_1667226 : Nat := 118140960795 + 1667226 * 2 ^ 59
def prefixEnd_1667226 : Nat := 4983230072969 + 3 ^ 40 * 1667226 * 2
def baseEnd_1667226 : Nat := 3522997109765428824311

theorem tailTrace_1667226 : CollatzResearch.WordTrace tailWord_1667226 prefixEnd_1667226 3522997109765428824311 := by
  unfold tailWord_1667226
  simp only [CollatzResearch.WordTrace]
  refine ⟨15202181964483104094159383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40539151905288277584425021 15202181964483104094159383)
  ·
    refine ⟨22803272946724656141239075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15202181964483104094159383 22803272946724656141239075)
    ·
      refine ⟨34204909420086984211858613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22803272946724656141239075 34204909420086984211858613)
      ·
        refine ⟨3206710258133154769861745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34204909420086984211858613 3206710258133154769861745)
        ·
          refine ⟨2405032693599866077396309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3206710258133154769861745 2405032693599866077396309)
          ·
            refine ⟨3522997109765428824311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2405032693599866077396309 3522997109765428824311)
            ·
              rfl

theorem cell23_1667226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 11].length) (baseStart_1667226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667226 prefixEnd_1667226 := by exact prefixLift 1667226
  have htrace : WordTrace (prefixWord ++ tailWord_1667226) baseStart_1667226 baseEnd_1667226 := by
    simpa [prefixWord, tailWord_1667226, baseEnd_1667226] using wordTrace_append hprefix tailTrace_1667226
  have hstable : (prefixWord ++ tailWord_1667226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667226).length < 2 ^ (prefixWord ++ tailWord_1667226).sum := by decide
  have hdescent : baseEnd_1667226 < baseStart_1667226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667237 : List Nat := [1, 3, 1, 2, 1, 3, 3, 4, 1, 2, 2]
def baseStart_1667237 : Nat := 118140960795 + 1667237 * 2 ^ 59
def prefixEnd_1667237 : Nat := 4983230072969 + 3 ^ 40 * 1667237 * 2
def baseEnd_1667237 : Nat := 856093945960198661270023

theorem tailTrace_1667237 : CollatzResearch.WordTrace tailWord_1667237 prefixEnd_1667237 856093945960198661270023 := by
  unfold tailWord_1667237
  simp only [CollatzResearch.WordTrace]
  refine ⟨60809129060892565255287965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40539419373928376836858643 60809129060892565255287965)
  ·
    refine ⟨22803423397834711970732987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60809129060892565255287965 22803423397834711970732987)
    ·
      refine ⟨34205135096752067956099481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22803423397834711970732987 34205135096752067956099481)
      ·
        refine ⟨25653851322564050967074611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34205135096752067956099481 25653851322564050967074611)
        ·
          refine ⟨38480776983846076450611917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25653851322564050967074611 38480776983846076450611917)
          ·
            refine ⟨14430291368942278668979469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38480776983846076450611917 14430291368942278668979469)
            ·
              refine ⟨5411359263353354500867301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14430291368942278668979469 5411359263353354500867301)
              ·
                refine ⟨1014629861878753968912619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5411359263353354500867301 1014629861878753968912619)
                ·
                  refine ⟨1521944792818130953368929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014629861878753968912619 1521944792818130953368929)
                  ·
                    refine ⟨1141458594613598215026697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1521944792818130953368929 1141458594613598215026697)
                    ·
                      refine ⟨856093945960198661270023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1141458594613598215026697 856093945960198661270023)
                      ·
                        rfl

theorem cell23_1667237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_1667237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667237 prefixEnd_1667237 := by exact prefixLift 1667237
  have htrace : WordTrace (prefixWord ++ tailWord_1667237) baseStart_1667237 baseEnd_1667237 := by
    simpa [prefixWord, tailWord_1667237, baseEnd_1667237] using wordTrace_append hprefix tailTrace_1667237
  have hstable : (prefixWord ++ tailWord_1667237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667237).length < 2 ^ (prefixWord ++ tailWord_1667237).sum := by decide
  have hdescent : baseEnd_1667237 < baseStart_1667237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667303 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 2, 6]
def baseStart_1667303 : Nat := 118140960795 + 1667303 * 2 ^ 59
def prefixEnd_1667303 : Nat := 4983230072969 + 3 ^ 40 * 1667303 * 2
def baseEnd_1667303 : Nat := 285375945227798467681573

theorem tailTrace_1667303 : CollatzResearch.WordTrace tailWord_1667303 prefixEnd_1667303 285375945227798467681573 := by
  unfold tailWord_1667303
  simp only [CollatzResearch.WordTrace]
  refine ⟨60811536278653458527190563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40541024185768972351460375 60811536278653458527190563)
  ·
    refine ⟨91217304417980187790785845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60811536278653458527190563 91217304417980187790785845)
    ·
      refine ⟨8551622289185642605386173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91217304417980187790785845 8551622289185642605386173)
      ·
        refine ⟨3206858358444615977019815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8551622289185642605386173 3206858358444615977019815)
        ·
          refine ⟨4810287537666923965529723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206858358444615977019815 4810287537666923965529723)
          ·
            refine ⟨7215431306500385948294585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4810287537666923965529723 7215431306500385948294585)
            ·
              refine ⟨5411573479875289461220939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7215431306500385948294585 5411573479875289461220939)
              ·
                refine ⟨8117360219812934191831409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5411573479875289461220939 8117360219812934191831409)
                ·
                  refine ⟨6088020164859700643873557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8117360219812934191831409 6088020164859700643873557)
                  ·
                    refine ⟨285375945227798467681573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6088020164859700643873557 285375945227798467681573)
                    ·
                      rfl

theorem cell23_1667303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_1667303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667303 prefixEnd_1667303 := by exact prefixLift 1667303
  have htrace : WordTrace (prefixWord ++ tailWord_1667303) baseStart_1667303 baseEnd_1667303 := by
    simpa [prefixWord, tailWord_1667303, baseEnd_1667303] using wordTrace_append hprefix tailTrace_1667303
  have hstable : (prefixWord ++ tailWord_1667303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667303).length < 2 ^ (prefixWord ++ tailWord_1667303).sum := by decide
  have hdescent : baseEnd_1667303 < baseStart_1667303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667330 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1667330 : Nat := 118140960795 + 1667330 * 2 ^ 59
def prefixEnd_1667330 : Nat := 4983230072969 + 3 ^ 40 * 1667330 * 2
def baseEnd_1667330 : Nat := 856141699661066797407095

theorem tailTrace_1667330 : CollatzResearch.WordTrace tailWord_1667330 prefixEnd_1667330 856141699661066797407095 := by
  unfold tailWord_1667330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15203130262388910534605861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40541680699703761425615629 15203130262388910534605861)
  ·
    refine ⟨2850586924197920725238599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15203130262388910534605861 2850586924197920725238599)
    ·
      refine ⟨4275880386296881087857899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850586924197920725238599 4275880386296881087857899)
      ·
        refine ⟨6413820579445321631786849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275880386296881087857899 6413820579445321631786849)
        ·
          refine ⟨4810365434583991223840137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6413820579445321631786849 4810365434583991223840137)
          ·
            refine ⟨3607774075937993417880103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4810365434583991223840137 3607774075937993417880103)
            ·
              refine ⟨5411661113906990126820155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607774075937993417880103 5411661113906990126820155)
              ·
                refine ⟨8117491670860485190230233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5411661113906990126820155 8117491670860485190230233)
                ·
                  refine ⟨6088118753145363892672675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8117491670860485190230233 6088118753145363892672675)
                  ·
                    refine ⟨9132178129718045839009013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6088118753145363892672675 9132178129718045839009013)
                    ·
                      refine ⟨856141699661066797407095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9132178129718045839009013 856141699661066797407095)
                      ·
                        rfl

theorem cell23_1667330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1667330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667330 prefixEnd_1667330 := by exact prefixLift 1667330
  have htrace : WordTrace (prefixWord ++ tailWord_1667330) baseStart_1667330 baseEnd_1667330 := by
    simpa [prefixWord, tailWord_1667330, baseEnd_1667330] using wordTrace_append hprefix tailTrace_1667330
  have hstable : (prefixWord ++ tailWord_1667330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667330).length < 2 ^ (prefixWord ++ tailWord_1667330).sum := by decide
  have hdescent : baseEnd_1667330 < baseStart_1667330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667333 : List Nat := [1, 3, 1, 1, 2, 1, 2, 7, 5]
def baseStart_1667333 : Nat := 118140960795 + 1667333 * 2 ^ 59
def prefixEnd_1667333 : Nat := 4983230072969 + 3 ^ 40 * 1667333 * 2
def baseEnd_1667333 : Nat := 95127026678114476185509

theorem tailTrace_1667333 : CollatzResearch.WordTrace tailWord_1667333 prefixEnd_1667333 95127026678114476185509 := by
  unfold tailWord_1667333
  simp only [CollatzResearch.WordTrace]
  refine ⟨60812630468544773650782653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40541753645696515767188435 60812630468544773650782653)
  ·
    refine ⟨22804736425704290119043495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60812630468544773650782653 22804736425704290119043495)
    ·
      refine ⟨34207104638556435178565243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22804736425704290119043495 34207104638556435178565243)
      ·
        refine ⟨51310656957834652767847865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34207104638556435178565243 51310656957834652767847865)
        ·
          refine ⟨38482992718375989575885899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51310656957834652767847865 38482992718375989575885899)
          ·
            refine ⟨57724489077563984363828849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38482992718375989575885899 57724489077563984363828849)
            ·
              refine ⟨43293366808172988272871637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57724489077563984363828849 43293366808172988272871637)
              ·
                refine ⟨1014688284566554412645429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43293366808172988272871637 1014688284566554412645429)
                ·
                  refine ⟨95127026678114476185509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1014688284566554412645429 95127026678114476185509)
                  ·
                    rfl

theorem cell23_1667333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_1667333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667333 prefixEnd_1667333 := by exact prefixLift 1667333
  have htrace : WordTrace (prefixWord ++ tailWord_1667333) baseStart_1667333 baseEnd_1667333 := by
    simpa [prefixWord, tailWord_1667333, baseEnd_1667333] using wordTrace_append hprefix tailTrace_1667333
  have hstable : (prefixWord ++ tailWord_1667333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667333).length < 2 ^ (prefixWord ++ tailWord_1667333).sum := by decide
  have hdescent : baseEnd_1667333 < baseStart_1667333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667380 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1667380 : Nat := 118140960795 + 1667380 * 2 ^ 59
def prefixEnd_1667380 : Nat := 4983230072969 + 3 ^ 40 * 1667380 * 2
def baseEnd_1667380 : Nat := 285389124564597200593955

theorem tailTrace_1667380 : CollatzResearch.WordTrace tailWord_1667380 prefixEnd_1667380 285389124564597200593955 := by
  unfold tailWord_1667380
  simp only [CollatzResearch.WordTrace]
  refine ⟨30407172349687250338871797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40542896466249667118495729 30407172349687250338871797)
  ·
    refine ⟨2850672407783179719269231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30407172349687250338871797 2850672407783179719269231)
    ·
      refine ⟨4276008611674769578903847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850672407783179719269231 4276008611674769578903847)
      ·
        refine ⟨6414012917512154368355771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276008611674769578903847 6414012917512154368355771)
        ·
          refine ⟨9621019376268231552533657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6414012917512154368355771 9621019376268231552533657)
          ·
            refine ⟨7215764532201173664400243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9621019376268231552533657 7215764532201173664400243)
            ·
              refine ⟨10823646798301760496600365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7215764532201173664400243 10823646798301760496600365)
              ·
                refine ⟨4058867549363160186225137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10823646798301760496600365 4058867549363160186225137)
                ·
                  refine ⟨3044150662022370139668853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4058867549363160186225137 3044150662022370139668853)
                  ·
                    refine ⟨285389124564597200593955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3044150662022370139668853 285389124564597200593955)
                    ·
                      rfl

theorem cell23_1667380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1667380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667380 prefixEnd_1667380 := by exact prefixLift 1667380
  have htrace : WordTrace (prefixWord ++ tailWord_1667380) baseStart_1667380 baseEnd_1667380 := by
    simpa [prefixWord, tailWord_1667380, baseEnd_1667380] using wordTrace_append hprefix tailTrace_1667380
  have hstable : (prefixWord ++ tailWord_1667380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667380).length < 2 ^ (prefixWord ++ tailWord_1667380).sum := by decide
  have hdescent : baseEnd_1667380 < baseStart_1667380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667403 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 3]
def baseStart_1667403 : Nat := 118140960795 + 1667403 * 2 ^ 59
def prefixEnd_1667403 : Nat := 4983230072969 + 3 ^ 40 * 1667403 * 2
def baseEnd_1667403 : Nat := 856179183748845011794259

theorem tailTrace_1667403 : CollatzResearch.WordTrace tailWord_1667403 prefixEnd_1667403 856179183748845011794259 := by
  unfold tailWord_1667403
  simp only [CollatzResearch.WordTrace]
  refine ⟨60815183578291175605830863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40543455718860783737220575 60815183578291175605830863)
  ·
    refine ⟨91222775367436763408746295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60815183578291175605830863 91222775367436763408746295)
    ·
      refine ⟨136834163051155145113119443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91222775367436763408746295 136834163051155145113119443)
      ·
        refine ⟨205251244576732717669679165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136834163051155145113119443 205251244576732717669679165)
        ·
          refine ⟨76969216716274769126129687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205251244576732717669679165 76969216716274769126129687)
          ·
            refine ⟨115453825074412153689194531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76969216716274769126129687 115453825074412153689194531)
            ·
              refine ⟨173180737611618230533791797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115453825074412153689194531 173180737611618230533791797)
              ·
                refine ⟨16235694151089209112542981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173180737611618230533791797 16235694151089209112542981)
                ·
                  refine ⟨3044192653329226708601809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16235694151089209112542981 3044192653329226708601809)
                  ·
                    refine ⟨2283144489996920031451357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3044192653329226708601809 2283144489996920031451357)
                    ·
                      refine ⟨856179183748845011794259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2283144489996920031451357 856179183748845011794259)
                      ·
                        rfl

theorem cell23_1667403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 3].length) (baseStart_1667403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667403 prefixEnd_1667403 := by exact prefixLift 1667403
  have htrace : WordTrace (prefixWord ++ tailWord_1667403) baseStart_1667403 baseEnd_1667403 := by
    simpa [prefixWord, tailWord_1667403, baseEnd_1667403] using wordTrace_append hprefix tailTrace_1667403
  have hstable : (prefixWord ++ tailWord_1667403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667403).length < 2 ^ (prefixWord ++ tailWord_1667403).sum := by decide
  have hdescent : baseEnd_1667403 < baseStart_1667403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667423 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 6]
def baseStart_1667423 : Nat := 118140960795 + 1667423 * 2 ^ 59
def prefixEnd_1667423 : Nat := 4983230072969 + 3 ^ 40 * 1667423 * 2
def baseEnd_1667423 : Nat := 95132161484659437060463

theorem tailTrace_1667423 : CollatzResearch.WordTrace tailWord_1667423 prefixEnd_1667423 95132161484659437060463 := by
  unfold tailWord_1667423
  simp only [CollatzResearch.WordTrace]
  refine ⟨60815913038218719021558923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40543942025479146014372615 60815913038218719021558923)
  ·
    refine ⟨91223869557328078532338385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60815913038218719021558923 91223869557328078532338385)
    ·
      refine ⟨68417902167996058899253789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91223869557328078532338385 68417902167996058899253789)
      ·
        refine ⟨25656713312998522087220171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68417902167996058899253789 25656713312998522087220171)
        ·
          refine ⟨38485069969497783130830257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25656713312998522087220171 38485069969497783130830257)
          ·
            refine ⟨28863802477123337348122693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38485069969497783130830257 28863802477123337348122693)
            ·
              refine ⟨5411962964460625752773005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28863802477123337348122693 5411962964460625752773005)
              ·
                refine ⟨2029486111672734657289877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5411962964460625752773005 2029486111672734657289877)
                ·
                  refine ⟨95132161484659437060463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2029486111672734657289877 95132161484659437060463)
                  ·
                    rfl

theorem cell23_1667423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 6].length) (baseStart_1667423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667423 prefixEnd_1667423 := by exact prefixLift 1667423
  have htrace : WordTrace (prefixWord ++ tailWord_1667423) baseStart_1667423 baseEnd_1667423 := by
    simpa [prefixWord, tailWord_1667423, baseEnd_1667423] using wordTrace_append hprefix tailTrace_1667423
  have hstable : (prefixWord ++ tailWord_1667423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667423).length < 2 ^ (prefixWord ++ tailWord_1667423).sum := by decide
  have hdescent : baseEnd_1667423 < baseStart_1667423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667457 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 6]
def baseStart_1667457 : Nat := 118140960795 + 1667457 * 2 ^ 59
def prefixEnd_1667457 : Nat := 4983230072969 + 3 ^ 40 * 1667457 * 2
def baseEnd_1667457 : Nat := 95134101300465311168779

theorem tailTrace_1667457 : CollatzResearch.WordTrace tailWord_1667457 prefixEnd_1667457 95134101300465311168779 := by
  unfold tailWord_1667457
  simp only [CollatzResearch.WordTrace]
  refine ⟨60817153120095542828296625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40544768746730361885531083 60817153120095542828296625)
  ·
    refine ⟨45612864840071657121222469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60817153120095542828296625 45612864840071657121222469)
    ·
      refine ⟨8552412157513435710229213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45612864840071657121222469 8552412157513435710229213)
      ·
        refine ⟨3207154559067538391335955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8552412157513435710229213 3207154559067538391335955)
        ·
          refine ⟨4810731838601307587003933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3207154559067538391335955 4810731838601307587003933)
          ·
            refine ⟨1804024439475490345126475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4810731838601307587003933 1804024439475490345126475)
            ·
              refine ⟨2706036659213235517689713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804024439475490345126475 2706036659213235517689713)
              ·
                refine ⟨2029527494409926638267285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706036659213235517689713 2029527494409926638267285)
                ·
                  refine ⟨95134101300465311168779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2029527494409926638267285 95134101300465311168779)
                  ·
                    rfl

theorem cell23_1667457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 6].length) (baseStart_1667457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667457 prefixEnd_1667457 := by exact prefixLift 1667457
  have htrace : WordTrace (prefixWord ++ tailWord_1667457) baseStart_1667457 baseEnd_1667457 := by
    simpa [prefixWord, tailWord_1667457, baseEnd_1667457] using wordTrace_append hprefix tailTrace_1667457
  have hstable : (prefixWord ++ tailWord_1667457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667457).length < 2 ^ (prefixWord ++ tailWord_1667457).sum := by decide
  have hdescent : baseEnd_1667457 < baseStart_1667457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667467 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 3]
def baseStart_1667467 : Nat := 118140960795 + 1667467 * 2 ^ 59
def prefixEnd_1667467 : Nat := 4983230072969 + 3 ^ 40 * 1667467 * 2
def baseEnd_1667467 : Nat := 856212046510732761393965

theorem tailTrace_1667467 : CollatzResearch.WordTrace tailWord_1667467 prefixEnd_1667467 856212046510732761393965 := by
  unfold tailWord_1667467
  simp only [CollatzResearch.WordTrace]
  refine ⟨60817517850059314536160655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40545011900039543024107103 60817517850059314536160655)
  ·
    refine ⟨91226276775088971804240983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60817517850059314536160655 91226276775088971804240983)
    ·
      refine ⟨136839415162633457706361475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91226276775088971804240983 136839415162633457706361475)
      ·
        refine ⟨205259122743950186559542213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136839415162633457706361475 205259122743950186559542213)
        ·
          refine ⟨38486085514490659979914165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205259122743950186559542213 38486085514490659979914165)
          ·
            refine ⟨3608070516983499373116953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38486085514490659979914165 3608070516983499373116953)
            ·
              refine ⟨2706052887737624529837715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3608070516983499373116953 2706052887737624529837715)
              ·
                refine ⟨4059079331606436794756573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706052887737624529837715 4059079331606436794756573)
                ·
                  refine ⟨1522154749352413798033715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4059079331606436794756573 1522154749352413798033715)
                  ·
                    refine ⟨2283232124028620697050573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1522154749352413798033715 2283232124028620697050573)
                    ·
                      refine ⟨856212046510732761393965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2283232124028620697050573 856212046510732761393965)
                      ·
                        rfl

theorem cell23_1667467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 3].length) (baseStart_1667467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667467 prefixEnd_1667467 := by exact prefixLift 1667467
  have htrace : WordTrace (prefixWord ++ tailWord_1667467) baseStart_1667467 baseEnd_1667467 := by
    simpa [prefixWord, tailWord_1667467, baseEnd_1667467] using wordTrace_append hprefix tailTrace_1667467
  have hstable : (prefixWord ++ tailWord_1667467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667467).length < 2 ^ (prefixWord ++ tailWord_1667467).sum := by decide
  have hdescent : baseEnd_1667467 < baseStart_1667467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667493 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_1667493 : Nat := 118140960795 + 1667493 * 2 ^ 59
def prefixEnd_1667493 : Nat := 4983230072969 + 3 ^ 40 * 1667493 * 2
def baseEnd_1667493 : Nat := 856225397007749659668845

theorem tailTrace_1667493 : CollatzResearch.WordTrace tailWord_1667493 prefixEnd_1667493 856225397007749659668845 := by
  unfold tailWord_1667493
  simp only [CollatzResearch.WordTrace]
  refine ⟨60818466147965120976607133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40545644098643413984404755 60818466147965120976607133)
  ·
    refine ⟨22806924805486920366227675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60818466147965120976607133 22806924805486920366227675)
    ·
      refine ⟨34210387208230380549341513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22806924805486920366227675 34210387208230380549341513)
      ·
        refine ⟨25657790406172785412006135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34210387208230380549341513 25657790406172785412006135)
        ·
          refine ⟨38486685609259178118009203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25657790406172785412006135 38486685609259178118009203)
          ·
            refine ⟨57730028413888767177013805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38486685609259178118009203 57730028413888767177013805)
            ·
              refine ⟨21648760655208287691380177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57730028413888767177013805 21648760655208287691380177)
              ·
                refine ⟨16236570491406215768535133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21648760655208287691380177 16236570491406215768535133)
                ·
                  refine ⟨6088713934277330913200675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16236570491406215768535133 6088713934277330913200675)
                  ·
                    refine ⟨9133070901415996369801013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6088713934277330913200675 9133070901415996369801013)
                    ·
                      refine ⟨856225397007749659668845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9133070901415996369801013 856225397007749659668845)
                      ·
                        rfl

theorem cell23_1667493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_1667493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667493 prefixEnd_1667493 := by exact prefixLift 1667493
  have htrace : WordTrace (prefixWord ++ tailWord_1667493) baseStart_1667493 baseEnd_1667493 := by
    simpa [prefixWord, tailWord_1667493, baseEnd_1667493] using wordTrace_append hprefix tailTrace_1667493
  have hstable : (prefixWord ++ tailWord_1667493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667493).length < 2 ^ (prefixWord ++ tailWord_1667493).sum := by decide
  have hdescent : baseEnd_1667493 < baseStart_1667493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667513 : List Nat := [1, 2, 1, 4, 3, 1, 11]
def baseStart_1667513 : Nat := 118140960795 + 1667513 * 2 ^ 59
def prefixEnd_1667513 : Nat := 4983230072969 + 3 ^ 40 * 1667513 * 2
def baseEnd_1667513 : Nat := 10570810699022710881713

theorem tailTrace_1667513 : CollatzResearch.WordTrace tailWord_1667513 prefixEnd_1667513 10570810699022710881713 := by
  unfold tailWord_1667513
  simp only [CollatzResearch.WordTrace]
  refine ⟨60819195607892664392335193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40546130405261776261556795 60819195607892664392335193)
  ·
    refine ⟨45614396705919498294251395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60819195607892664392335193 45614396705919498294251395)
    ·
      refine ⟨68421595058879247441377093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45614396705919498294251395 68421595058879247441377093)
      ·
        refine ⟨12829049073539858895258205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68421595058879247441377093 12829049073539858895258205)
        ·
          refine ⟨4810893402577447085721827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12829049073539858895258205 4810893402577447085721827)
          ·
            refine ⟨7216340103866170628582741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4810893402577447085721827 7216340103866170628582741)
            ·
              refine ⟨10570810699022710881713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7216340103866170628582741 10570810699022710881713)
              ·
                rfl

theorem cell23_1667513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 11].length) (baseStart_1667513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667513 prefixEnd_1667513 := by exact prefixLift 1667513
  have htrace : WordTrace (prefixWord ++ tailWord_1667513) baseStart_1667513 baseEnd_1667513 := by
    simpa [prefixWord, tailWord_1667513, baseEnd_1667513] using wordTrace_append hprefix tailTrace_1667513
  have hstable : (prefixWord ++ tailWord_1667513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667513).length < 2 ^ (prefixWord ++ tailWord_1667513).sum := by decide
  have hdescent : baseEnd_1667513 < baseStart_1667513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667637 : List Nat := [1, 3, 3, 1, 1, 2, 1, 6, 5]
def baseStart_1667637 : Nat := 118140960795 + 1667637 * 2 ^ 59
def prefixEnd_1667637 : Nat := 4983230072969 + 3 ^ 40 * 1667637 * 2
def baseEnd_1667637 : Nat := 95144370913555232918687

theorem tailTrace_1667637 : CollatzResearch.WordTrace tailWord_1667637 prefixEnd_1667637 95144370913555232918687 := by
  unfold tailWord_1667637
  simp only [CollatzResearch.WordTrace]
  refine ⟨60823718259443433569849165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40549145506295622379899443 60823718259443433569849165)
  ·
    refine ⟨22808894347291287588693437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60823718259443433569849165 22808894347291287588693437)
    ·
      refine ⟨8553335380234232845760039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22808894347291287588693437 8553335380234232845760039)
      ·
        refine ⟨12830003070351349268640059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8553335380234232845760039 12830003070351349268640059)
        ·
          refine ⟨19245004605527023902960089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12830003070351349268640059 19245004605527023902960089)
          ·
            refine ⟨14433753454145267927220067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19245004605527023902960089 14433753454145267927220067)
            ·
              refine ⟨21650630181217901890830101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14433753454145267927220067 21650630181217901890830101)
              ·
                refine ⟨1014873289744589151132661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21650630181217901890830101 1014873289744589151132661)
                ·
                  refine ⟨95144370913555232918687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1014873289744589151132661 95144370913555232918687)
                  ·
                    rfl

theorem cell23_1667637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_1667637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667637 prefixEnd_1667637 := by exact prefixLift 1667637
  have htrace : WordTrace (prefixWord ++ tailWord_1667637) baseStart_1667637 baseEnd_1667637 := by
    simpa [prefixWord, tailWord_1667637, baseEnd_1667637] using wordTrace_append hprefix tailTrace_1667637
  have hstable : (prefixWord ++ tailWord_1667637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667637).length < 2 ^ (prefixWord ++ tailWord_1667637).sum := by decide
  have hdescent : baseEnd_1667637 < baseStart_1667637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667654 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_1667654 : Nat := 118140960795 + 1667654 * 2 ^ 59
def prefixEnd_1667654 : Nat := 4983230072969 + 3 ^ 40 * 1667654 * 2
def baseEnd_1667654 : Nat := 95145340821458169972845

theorem tailTrace_1667654 : CollatzResearch.WordTrace tailWord_1667654 prefixEnd_1667654 95145340821458169972845 := by
  unfold tailWord_1667654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900760571886932671038063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40549558866921230315478677 1900760571886932671038063)
  ·
    refine ⟨2851140857830399006557095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1900760571886932671038063 2851140857830399006557095)
    ·
      refine ⟨4276711286745598509835643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851140857830399006557095 4276711286745598509835643)
      ·
        refine ⟨6415066930118397764753465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276711286745598509835643 6415066930118397764753465)
        ·
          refine ⟨4811300197588798323565099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6415066930118397764753465 4811300197588798323565099)
          ·
            refine ⟨7216950296383197485347649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811300197588798323565099 7216950296383197485347649)
            ·
              refine ⟨5412712722287398114010737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216950296383197485347649 5412712722287398114010737)
              ·
                refine ⟨4059534541715548585508053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5412712722287398114010737 4059534541715548585508053)
                ·
                  refine ⟨95145340821458169972845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4059534541715548585508053 95145340821458169972845)
                  ·
                    rfl

theorem cell23_1667654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_1667654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667654 prefixEnd_1667654 := by exact prefixLift 1667654
  have htrace : WordTrace (prefixWord ++ tailWord_1667654) baseStart_1667654 baseEnd_1667654 := by
    simpa [prefixWord, tailWord_1667654, baseEnd_1667654] using wordTrace_append hprefix tailTrace_1667654
  have hstable : (prefixWord ++ tailWord_1667654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667654).length < 2 ^ (prefixWord ++ tailWord_1667654).sum := by decide
  have hdescent : baseEnd_1667654 < baseStart_1667654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667744 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 6]
def baseStart_1667744 : Nat := 118140960795 + 1667744 * 2 ^ 59
def prefixEnd_1667744 : Nat := 4983230072969 + 3 ^ 40 * 1667744 * 2
def baseEnd_1667744 : Nat := 95150475628003130847799

theorem tailTrace_1667744 : CollatzResearch.WordTrace tailWord_1667744 prefixEnd_1667744 95150475628003130847799 := by
  unfold tailWord_1667744
  simp only [CollatzResearch.WordTrace]
  refine ⟨30413810435027895421997143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40551747246703860562662857 30413810435027895421997143)
  ·
    refine ⟨45620715652541843132995715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30413810435027895421997143 45620715652541843132995715)
    ·
      refine ⟨68431073478812764699493573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45620715652541843132995715 68431073478812764699493573)
      ·
        refine ⟨12830826277277393381155045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68431073478812764699493573 12830826277277393381155045)
        ·
          refine ⟨2405779926989511258966571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12830826277277393381155045 2405779926989511258966571)
          ·
            refine ⟨3608669890484266888449857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405779926989511258966571 3608669890484266888449857)
            ·
              refine ⟨2706502417863200166337393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3608669890484266888449857 2706502417863200166337393)
              ·
                refine ⟨2029876813397400124753045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706502417863200166337393 2029876813397400124753045)
                ·
                  refine ⟨95150475628003130847799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2029876813397400124753045 95150475628003130847799)
                  ·
                    rfl

theorem cell23_1667744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 6].length) (baseStart_1667744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667744 prefixEnd_1667744 := by exact prefixLift 1667744
  have htrace : WordTrace (prefixWord ++ tailWord_1667744) baseStart_1667744 baseEnd_1667744 := by
    simpa [prefixWord, tailWord_1667744, baseEnd_1667744] using wordTrace_append hprefix tailTrace_1667744
  have hstable : (prefixWord ++ tailWord_1667744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667744).length < 2 ^ (prefixWord ++ tailWord_1667744).sum := by decide
  have hdescent : baseEnd_1667744 < baseStart_1667744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667774 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1667774 : Nat := 118140960795 + 1667774 * 2 ^ 59
def prefixEnd_1667774 : Nat := 4983230072969 + 3 ^ 40 * 1667774 * 2
def baseEnd_1667774 : Nat := 285456561690554353418351

theorem tailTrace_1667774 : CollatzResearch.WordTrace tailWord_1667774 prefixEnd_1667774 285456561690554353418351 := by
  unfold tailWord_1667774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7603589382493388245948297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40552476706631403978390917 7603589382493388245948297)
  ·
    refine ⟨5702692036870041184461223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7603589382493388245948297 5702692036870041184461223)
    ·
      refine ⟨8554038055305061776691835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5702692036870041184461223 8554038055305061776691835)
      ·
        refine ⟨12831057082957592665037753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8554038055305061776691835 12831057082957592665037753)
        ·
          refine ⟨9623292812218194498778315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12831057082957592665037753 9623292812218194498778315)
          ·
            refine ⟨14434939218327291748167473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9623292812218194498778315 14434939218327291748167473)
            ·
              refine ⟨10826204413745468811125605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14434939218327291748167473 10826204413745468811125605)
              ·
                refine ⟨2029913327577275402086051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10826204413745468811125605 2029913327577275402086051)
                ·
                  refine ⟨3044869991365913103129077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029913327577275402086051 3044869991365913103129077)
                  ·
                    refine ⟨285456561690554353418351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3044869991365913103129077 285456561690554353418351)
                    ·
                      rfl

theorem cell23_1667774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1667774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667774 prefixEnd_1667774 := by exact prefixLift 1667774
  have htrace : WordTrace (prefixWord ++ tailWord_1667774) baseStart_1667774 baseEnd_1667774 := by
    simpa [prefixWord, tailWord_1667774, baseEnd_1667774] using wordTrace_append hprefix tailTrace_1667774
  have hstable : (prefixWord ++ tailWord_1667774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667774).length < 2 ^ (prefixWord ++ tailWord_1667774).sum := by decide
  have hdescent : baseEnd_1667774 < baseStart_1667774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667782 : List Nat := [6, 1, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1667782 : Nat := 118140960795 + 1667782 * 2 ^ 59
def prefixEnd_1667782 : Nat := 4983230072969 + 3 ^ 40 * 1667782 * 2
def baseEnd_1667782 : Nat := 285457930972299676318339

theorem tailTrace_1667782 : CollatzResearch.WordTrace tailWord_1667782 prefixEnd_1667782 285457930972299676318339 := by
  unfold tailWord_1667782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900906463872441354183675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40552671229278748889251733 1900906463872441354183675)
  ·
    refine ⟨2851359695808662031275513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1900906463872441354183675 2851359695808662031275513)
    ·
      refine ⟨2138519771856496523456635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2851359695808662031275513 2138519771856496523456635)
      ·
        refine ⟨3207779657784744785184953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2138519771856496523456635 3207779657784744785184953)
        ·
          refine ⟨2405834743338558588888715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3207779657784744785184953 2405834743338558588888715)
          ·
            refine ⟨3608752115007837883333073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405834743338558588888715 3608752115007837883333073)
            ·
              refine ⟨2706564086255878412499805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3608752115007837883333073 2706564086255878412499805)
              ·
                refine ⟨1014961532345954404687427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2706564086255878412499805 1014961532345954404687427)
                ·
                  refine ⟨1522442298518931607031141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014961532345954404687427 1522442298518931607031141)
                  ·
                    refine ⟨285457930972299676318339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1522442298518931607031141 285457930972299676318339)
                    ·
                      rfl

theorem cell23_1667782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1667782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667782 prefixEnd_1667782 := by exact prefixLift 1667782
  have htrace : WordTrace (prefixWord ++ tailWord_1667782) baseStart_1667782 baseEnd_1667782 := by
    simpa [prefixWord, tailWord_1667782, baseEnd_1667782] using wordTrace_append hprefix tailTrace_1667782
  have hstable : (prefixWord ++ tailWord_1667782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667782).length < 2 ^ (prefixWord ++ tailWord_1667782).sum := by decide
  have hdescent : baseEnd_1667782 < baseStart_1667782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667788 : List Nat := [2, 2, 1, 5, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1667788 : Nat := 118140960795 + 1667788 * 2 ^ 59
def prefixEnd_1667788 : Nat := 4983230072969 + 3 ^ 40 * 1667788 * 2
def baseEnd_1667788 : Nat := 856376873800826005479989

theorem tailTrace_1667788 : CollatzResearch.WordTrace tailWord_1667788 prefixEnd_1667788 856376873800826005479989 := by
  unfold tailWord_1667788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30414612840948193179298009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40552817121264257572397345 30414612840948193179298009)
  ·
    refine ⟨22810959630711144884473507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30414612840948193179298009 22810959630711144884473507)
    ·
      refine ⟨34216439446066717326710261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22810959630711144884473507 34216439446066717326710261)
      ·
        refine ⟨3207791198068754749379087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34216439446066717326710261 3207791198068754749379087)
        ·
          refine ⟨4811686797103132124068631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3207791198068754749379087 4811686797103132124068631)
          ·
            refine ⟨7217530195654698186102947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811686797103132124068631 7217530195654698186102947)
            ·
              refine ⟨10826295293482047279154421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217530195654698186102947 10826295293482047279154421)
              ·
                refine ⟨1014965183763941932420727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10826295293482047279154421 1014965183763941932420727)
                ·
                  refine ⟨1522447775645912898631091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014965183763941932420727 1522447775645912898631091)
                  ·
                    refine ⟨2283671663468869347946637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1522447775645912898631091 2283671663468869347946637)
                    ·
                      refine ⟨856376873800826005479989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2283671663468869347946637 856376873800826005479989)
                      ·
                        rfl

theorem cell23_1667788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1667788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667788 prefixEnd_1667788 := by exact prefixLift 1667788
  have htrace : WordTrace (prefixWord ++ tailWord_1667788) baseStart_1667788 baseEnd_1667788 := by
    simpa [prefixWord, tailWord_1667788, baseEnd_1667788] using wordTrace_append hprefix tailTrace_1667788
  have hstable : (prefixWord ++ tailWord_1667788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667788).length < 2 ^ (prefixWord ++ tailWord_1667788).sum := by decide
  have hdescent : baseEnd_1667788 < baseStart_1667788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667844 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1667844 : Nat := 118140960795 + 1667844 * 2 ^ 59
def prefixEnd_1667844 : Nat := 4983230072969 + 3 ^ 40 * 1667844 * 2
def baseEnd_1667844 : Nat := 856405628717477786379731

theorem tailTrace_1667844 : CollatzResearch.WordTrace tailWord_1667844 prefixEnd_1667844 856405628717477786379731 := by
  unfold tailWord_1667844
  simp only [CollatzResearch.WordTrace]
  refine ⟨30415634084846753961317293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40554178779795671948423057 30415634084846753961317293)
  ·
    refine ⟨11405862781817532735493985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30415634084846753961317293 11405862781817532735493985)
    ·
      refine ⟨8554397086363149551620489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11405862781817532735493985 8554397086363149551620489)
      ·
        refine ⟨6415797814772362163715367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8554397086363149551620489 6415797814772362163715367)
        ·
          refine ⟨9623696722158543245573051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6415797814772362163715367 9623696722158543245573051)
          ·
            refine ⟨14435545083237814868359577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9623696722158543245573051 14435545083237814868359577)
            ·
              refine ⟨10826658812428361151269683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14435545083237814868359577 10826658812428361151269683)
              ·
                refine ⟨16239988218642541726904525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10826658812428361151269683 16239988218642541726904525)
                ·
                  refine ⟨6089995581990953147589197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16239988218642541726904525 6089995581990953147589197)
                  ·
                    refine ⟨2283748343246607430345949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6089995581990953147589197 2283748343246607430345949)
                    ·
                      refine ⟨856405628717477786379731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2283748343246607430345949 856405628717477786379731)
                      ·
                        rfl

theorem cell23_1667844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1667844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667844 prefixEnd_1667844 := by exact prefixLift 1667844
  have htrace : WordTrace (prefixWord ++ tailWord_1667844) baseStart_1667844 baseEnd_1667844 := by
    simpa [prefixWord, tailWord_1667844, baseEnd_1667844] using wordTrace_append hprefix tailTrace_1667844
  have hstable : (prefixWord ++ tailWord_1667844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667844).length < 2 ^ (prefixWord ++ tailWord_1667844).sum := by decide
  have hdescent : baseEnd_1667844 < baseStart_1667844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667861 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_1667861 : Nat := 118140960795 + 1667861 * 2 ^ 59
def prefixEnd_1667861 : Nat := 4983230072969 + 3 ^ 40 * 1667861 * 2
def baseEnd_1667861 : Nat := 856414357888604219867153

theorem tailTrace_1667861 : CollatzResearch.WordTrace tailWord_1667861 prefixEnd_1667861 856414357888604219867153 := by
  unfold tailWord_1667861
  simp only [CollatzResearch.WordTrace]
  refine ⟨60831888210631919826003437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40554592140421279884002291 60831888210631919826003437)
  ·
    refine ⟨22811958078986969934751289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60831888210631919826003437 22811958078986969934751289)
    ·
      refine ⟨17108968559240227451063467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22811958078986969934751289 17108968559240227451063467)
      ·
        refine ⟨25663452838860341176595201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17108968559240227451063467 25663452838860341176595201)
        ·
          refine ⟨19247589629145255882446401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25663452838860341176595201 19247589629145255882446401)
          ·
            refine ⟨14435692221858941911834801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19247589629145255882446401 14435692221858941911834801)
            ·
              refine ⟨10826769166394206433876101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14435692221858941911834801 10826769166394206433876101)
              ·
                refine ⟨2030019218698913706351769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10826769166394206433876101 2030019218698913706351769)
                ·
                  refine ⟨1522514414024185279763827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2030019218698913706351769 1522514414024185279763827)
                  ·
                    refine ⟨2283771621036277919645741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1522514414024185279763827 2283771621036277919645741)
                    ·
                      refine ⟨856414357888604219867153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2283771621036277919645741 856414357888604219867153)
                      ·
                        rfl

theorem cell23_1667861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_1667861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667861 prefixEnd_1667861 := by exact prefixLift 1667861
  have htrace : WordTrace (prefixWord ++ tailWord_1667861) baseStart_1667861 baseEnd_1667861 := by
    simpa [prefixWord, tailWord_1667861, baseEnd_1667861] using wordTrace_append hprefix tailTrace_1667861
  have hstable : (prefixWord ++ tailWord_1667861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667861).length < 2 ^ (prefixWord ++ tailWord_1667861).sum := by decide
  have hdescent : baseEnd_1667861 < baseStart_1667861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667877 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_1667877 : Nat := 118140960795 + 1667877 * 2 ^ 59
def prefixEnd_1667877 : Nat := 4983230072969 + 3 ^ 40 * 1667877 * 2
def baseEnd_1667877 : Nat := 285474191193025385755693

theorem tailTrace_1667877 : CollatzResearch.WordTrace tailWord_1667877 prefixEnd_1667877 285474191193025385755693 := by
  unfold tailWord_1667877
  simp only [CollatzResearch.WordTrace]
  refine ⟨60832471778573954558585885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40554981185715969705723923 60832471778573954558585885)
  ·
    refine ⟨22812176916965232959469707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60832471778573954558585885 22812176916965232959469707)
    ·
      refine ⟨34218265375447849439204561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22812176916965232959469707 34218265375447849439204561)
      ·
        refine ⟨25663699031585887079403421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34218265375447849439204561 25663699031585887079403421)
        ·
          refine ⟨9623887136844707654776283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25663699031585887079403421 9623887136844707654776283)
          ·
            refine ⟨14435830705267061482164425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9623887136844707654776283 14435830705267061482164425)
            ·
              refine ⟨10826873028950296111623319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14435830705267061482164425 10826873028950296111623319)
              ·
                refine ⟨16240309543425444167434979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10826873028950296111623319 16240309543425444167434979)
                ·
                  refine ⟨24360464315138166251152469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16240309543425444167434979 24360464315138166251152469)
                  ·
                    refine ⟨285474191193025385755693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24360464315138166251152469 285474191193025385755693)
                    ·
                      rfl

theorem cell23_1667877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_1667877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667877 prefixEnd_1667877 := by exact prefixLift 1667877
  have htrace : WordTrace (prefixWord ++ tailWord_1667877) baseStart_1667877 baseEnd_1667877 := by
    simpa [prefixWord, tailWord_1667877, baseEnd_1667877] using wordTrace_append hprefix tailTrace_1667877
  have hstable : (prefixWord ++ tailWord_1667877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667877).length < 2 ^ (prefixWord ++ tailWord_1667877).sum := by decide
  have hdescent : baseEnd_1667877 < baseStart_1667877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667882 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1667882 : Nat := 118140960795 + 1667882 * 2 ^ 59
def prefixEnd_1667882 : Nat := 4983230072969 + 3 ^ 40 * 1667882 * 2
def baseEnd_1667882 : Nat := 856425140982348637704557

theorem tailTrace_1667882 : CollatzResearch.WordTrace tailWord_1667882 prefixEnd_1667882 856425140982348637704557 := by
  unfold tailWord_1667882
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208163535888960103129475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40555102762370560275011933 15208163535888960103129475)
  ·
    refine ⟨22812245303833440154694213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15208163535888960103129475 22812245303833440154694213)
    ·
      refine ⟨4277295994468770029005165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22812245303833440154694213 4277295994468770029005165)
      ·
        refine ⟨1603985997925788760876937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4277295994468770029005165 1603985997925788760876937)
        ·
          refine ⟨1202989498444341570657703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603985997925788760876937 1202989498444341570657703)
          ·
            refine ⟨1804484247666512355986555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202989498444341570657703 1804484247666512355986555)
            ·
              refine ⟨2706726371499768533979833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804484247666512355986555 2706726371499768533979833)
              ·
                refine ⟨2030044778624826400484875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706726371499768533979833 2030044778624826400484875)
                ·
                  refine ⟨3045067167937239600727313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030044778624826400484875 3045067167937239600727313)
                  ·
                    refine ⟨2283800375952929700545485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3045067167937239600727313 2283800375952929700545485)
                    ·
                      refine ⟨856425140982348637704557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2283800375952929700545485 856425140982348637704557)
                      ·
                        rfl

theorem cell23_1667882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1667882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667882 prefixEnd_1667882 := by exact prefixLift 1667882
  have htrace : WordTrace (prefixWord ++ tailWord_1667882) baseStart_1667882 baseEnd_1667882 := by
    simpa [prefixWord, tailWord_1667882, baseEnd_1667882] using wordTrace_append hprefix tailTrace_1667882
  have hstable : (prefixWord ++ tailWord_1667882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667882).length < 2 ^ (prefixWord ++ tailWord_1667882).sum := by decide
  have hdescent : baseEnd_1667882 < baseStart_1667882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667947 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 7]
def baseStart_1667947 : Nat := 118140960795 + 1667947 * 2 ^ 59
def prefixEnd_1667947 : Nat := 4983230072969 + 3 ^ 40 * 1667947 * 2
def baseEnd_1667947 : Nat := 856458517224890883391757

theorem tailTrace_1667947 : CollatzResearch.WordTrace tailWord_1667947 prefixEnd_1667947 856458517224890883391757 := by
  unfold tailWord_1667947
  simp only [CollatzResearch.WordTrace]
  refine ⟨60835024888320356513634095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40556683258880237675756063 60835024888320356513634095)
  ·
    refine ⟨91252537332480534770451143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60835024888320356513634095 91252537332480534770451143)
    ·
      refine ⟨136878805998720802155676715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91252537332480534770451143 136878805998720802155676715)
      ·
        refine ⟨205318208998081203233515073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136878805998720802155676715 205318208998081203233515073)
        ·
          refine ⟨153988656748560902425136305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205318208998081203233515073 153988656748560902425136305)
          ·
            refine ⟨115491492561420676818852229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153988656748560902425136305 115491492561420676818852229)
            ·
              refine ⟨21654654855266376903534793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115491492561420676818852229 21654654855266376903534793)
              ·
                refine ⟨16240991141449782677651095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21654654855266376903534793 16240991141449782677651095)
                ·
                  refine ⟨24361486712174674016476643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16240991141449782677651095 24361486712174674016476643)
                  ·
                    refine ⟨36542230068262011024714965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24361486712174674016476643 36542230068262011024714965)
                    ·
                      refine ⟨856458517224890883391757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36542230068262011024714965 856458517224890883391757)
                      ·
                        rfl

theorem cell23_1667947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_1667947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667947 prefixEnd_1667947 := by exact prefixLift 1667947
  have htrace : WordTrace (prefixWord ++ tailWord_1667947) baseStart_1667947 baseEnd_1667947 := by
    simpa [prefixWord, tailWord_1667947, baseEnd_1667947] using wordTrace_append hprefix tailTrace_1667947
  have hstable : (prefixWord ++ tailWord_1667947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667947).length < 2 ^ (prefixWord ++ tailWord_1667947).sum := by decide
  have hdescent : baseEnd_1667947 < baseStart_1667947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667958 : List Nat := [5, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_1667958 : Nat := 118140960795 + 1667958 * 2 ^ 59
def prefixEnd_1667958 : Nat := 4983230072969 + 3 ^ 40 * 1667958 * 2
def baseEnd_1667958 : Nat := 95162685056898926706023

theorem tailTrace_1667958 : CollatzResearch.WordTrace tailWord_1667958 prefixEnd_1667958 95162685056898926706023 := by
  unfold tailWord_1667958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802214130705031587017783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40556950727520336928189685 3802214130705031587017783)
  ·
    refine ⟨5703321196057547380526675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3802214130705031587017783 5703321196057547380526675)
    ·
      refine ⟨8554981794086321070790013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703321196057547380526675 8554981794086321070790013)
      ·
        refine ⟨3208118172782370401546255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8554981794086321070790013 3208118172782370401546255)
        ·
          refine ⟨4812177259173555602319383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208118172782370401546255 4812177259173555602319383)
          ·
            refine ⟨7218265888760333403479075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812177259173555602319383 7218265888760333403479075)
            ·
              refine ⟨10827398833140500105218613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7218265888760333403479075 10827398833140500105218613)
              ·
                refine ⟨1015068640606921884864245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10827398833140500105218613 1015068640606921884864245)
                ·
                  refine ⟨95162685056898926706023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1015068640606921884864245 95162685056898926706023)
                  ·
                    rfl

theorem cell23_1667958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_1667958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667958 prefixEnd_1667958 := by exact prefixLift 1667958
  have htrace : WordTrace (prefixWord ++ tailWord_1667958) baseStart_1667958 baseEnd_1667958 := by
    simpa [prefixWord, tailWord_1667958, baseEnd_1667958] using wordTrace_append hprefix tailTrace_1667958
  have hstable : (prefixWord ++ tailWord_1667958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667958).length < 2 ^ (prefixWord ++ tailWord_1667958).sum := by decide
  have hdescent : baseEnd_1667958 < baseStart_1667958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667991 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 2, 4, 2]
def baseStart_1667991 : Nat := 118140960795 + 1667991 * 2 ^ 59
def prefixEnd_1667991 : Nat := 4983230072969 + 3 ^ 40 * 1667991 * 2
def baseEnd_1667991 : Nat := 856481110373688711241555

theorem tailTrace_1667991 : CollatzResearch.WordTrace tailWord_1667991 prefixEnd_1667991 856481110373688711241555 := by
  unfold tailWord_1667991
  simp only [CollatzResearch.WordTrace]
  refine ⟨60836629700160952028235827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40557753133440634685490551 60836629700160952028235827)
  ·
    refine ⟨91254944550241428042353741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60836629700160952028235827 91254944550241428042353741)
    ·
      refine ⟨34220604206340535515882653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91254944550241428042353741 34220604206340535515882653)
      ·
        refine ⟨12832726577377700818455995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34220604206340535515882653 12832726577377700818455995)
        ·
          refine ⟨19249089866066551227683993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832726577377700818455995 19249089866066551227683993)
          ·
            refine ⟨14436817399549913420762995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19249089866066551227683993 14436817399549913420762995)
            ·
              refine ⟨21655226099324870131144493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14436817399549913420762995 21655226099324870131144493)
              ·
                refine ⟨8120709787246826299179185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21655226099324870131144493 8120709787246826299179185)
                ·
                  refine ⟨6090532340435119724384389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8120709787246826299179185 6090532340435119724384389)
                  ·
                    refine ⟨1141974813831584948322073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6090532340435119724384389 1141974813831584948322073)
                    ·
                      refine ⟨856481110373688711241555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1141974813831584948322073 856481110373688711241555)
                      ·
                        rfl

theorem cell23_1667991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_1667991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667991 prefixEnd_1667991 := by exact prefixLift 1667991
  have htrace : WordTrace (prefixWord ++ tailWord_1667991) baseStart_1667991 baseEnd_1667991 := by
    simpa [prefixWord, tailWord_1667991, baseEnd_1667991] using wordTrace_append hprefix tailTrace_1667991
  have hstable : (prefixWord ++ tailWord_1667991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667991).length < 2 ^ (prefixWord ++ tailWord_1667991).sum := by decide
  have hdescent : baseEnd_1667991 < baseStart_1667991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668004 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_1668004 : Nat := 118140960795 + 1668004 * 2 ^ 59
def prefixEnd_1668004 : Nat := 4983230072969 + 3 ^ 40 * 1668004 * 2
def baseEnd_1668004 : Nat := 856487785622197160378995

theorem tailTrace_1668004 : CollatzResearch.WordTrace tailWord_1668004 prefixEnd_1668004 856487785622197160378995 := by
  unfold tailWord_1668004
  simp only [CollatzResearch.WordTrace]
  refine ⟨30418551924556927624229533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40558069232742570165639377 30418551924556927624229533)
  ·
    refine ⟨11406956971708847859086075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30418551924556927624229533 11406956971708847859086075)
    ·
      refine ⟨17110435457563271788629113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11406956971708847859086075 17110435457563271788629113)
      ·
        refine ⟨12832826593172453841471835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17110435457563271788629113 12832826593172453841471835)
        ·
          refine ⟨19249239889758680762207753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832826593172453841471835 19249239889758680762207753)
          ·
            refine ⟨14436929917319010571655815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19249239889758680762207753 14436929917319010571655815)
            ·
              refine ⟨21655394875978515857483723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14436929917319010571655815 21655394875978515857483723)
              ·
                refine ⟨32483092313967773786225585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21655394875978515857483723 32483092313967773786225585)
                ·
                  refine ⟨24362319235475830339669189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32483092313967773786225585 24362319235475830339669189)
                  ·
                    refine ⟨4567934856651718188687973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24362319235475830339669189 4567934856651718188687973)
                    ·
                      refine ⟨856487785622197160378995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4567934856651718188687973 856487785622197160378995)
                      ·
                        rfl

theorem cell23_1668004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_1668004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668004 prefixEnd_1668004 := by exact prefixLift 1668004
  have htrace : WordTrace (prefixWord ++ tailWord_1668004) baseStart_1668004 baseEnd_1668004 := by
    simpa [prefixWord, tailWord_1668004, baseEnd_1668004] using wordTrace_append hprefix tailTrace_1668004
  have hstable : (prefixWord ++ tailWord_1668004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668004).length < 2 ^ (prefixWord ++ tailWord_1668004).sum := by decide
  have hdescent : baseEnd_1668004 < baseStart_1668004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668022 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1668022 : Nat := 118140960795 + 1668022 * 2 ^ 59
def prefixEnd_1668022 : Nat := 4983230072969 + 3 ^ 40 * 1668022 * 2
def baseEnd_1668022 : Nat := 285499009424659363317971

theorem tailTrace_1668022 : CollatzResearch.WordTrace tailWord_1668022 prefixEnd_1668022 285499009424659363317971 := by
  unfold tailWord_1668022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802360022690540270163395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40558506908699096215076213 3802360022690540270163395)
  ·
    refine ⟨5703540034035810405245093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3802360022690540270163395 5703540034035810405245093)
    ·
      refine ⟨1069413756381714450983455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5703540034035810405245093 1069413756381714450983455)
      ·
        refine ⟨1604120634572571676475183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069413756381714450983455 1604120634572571676475183)
        ·
          refine ⟨2406180951858857514712775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604120634572571676475183 2406180951858857514712775)
          ·
            refine ⟨3609271427788286272069163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406180951858857514712775 3609271427788286272069163)
            ·
              refine ⟨5413907141682429408103745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609271427788286272069163 5413907141682429408103745)
              ·
                refine ⟨4060430356261822056077809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5413907141682429408103745 4060430356261822056077809)
                ·
                  refine ⟨3045322767196366542058357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4060430356261822056077809 3045322767196366542058357)
                  ·
                    refine ⟨285499009424659363317971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3045322767196366542058357 285499009424659363317971)
                    ·
                      rfl

theorem cell23_1668022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1668022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668022 prefixEnd_1668022 := by exact prefixLift 1668022
  have htrace : WordTrace (prefixWord ++ tailWord_1668022) baseStart_1668022 baseEnd_1668022 := by
    simpa [prefixWord, tailWord_1668022, baseEnd_1668022] using wordTrace_append hprefix tailTrace_1668022
  have hstable : (prefixWord ++ tailWord_1668022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668022).length < 2 ^ (prefixWord ++ tailWord_1668022).sum := by decide
  have hdescent : baseEnd_1668022 < baseStart_1668022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668092 : List Nat := [2, 2, 2, 1, 2, 3, 4, 2, 1, 1, 3]
def baseStart_1668092 : Nat := 118140960795 + 1668092 * 2 ^ 59
def prefixEnd_1668092 : Nat := 4983230072969 + 3 ^ 40 * 1668092 * 2
def baseEnd_1668092 : Nat := 856532971919792816078591

theorem tailTrace_1668092 : CollatzResearch.WordTrace tailWord_1668092 prefixEnd_1668092 856532971919792816078591 := by
  unfold tailWord_1668092
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420156736397523138831265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40560208981863364185108353 30420156736397523138831265)
  ·
    refine ⟨22815117552298142354123449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30420156736397523138831265 22815117552298142354123449)
    ·
      refine ⟨17111338164223606765592587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22815117552298142354123449 17111338164223606765592587)
      ·
        refine ⟨25667007246335410148388881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17111338164223606765592587 25667007246335410148388881)
        ·
          refine ⟨19250255434751557611291661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25667007246335410148388881 19250255434751557611291661)
          ·
            refine ⟨7218845788031834104234373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19250255434751557611291661 7218845788031834104234373)
            ·
              refine ⟨1353533585255968894543945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7218845788031834104234373 1353533585255968894543945)
              ·
                refine ⟨1015150188941976670907959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353533585255968894543945 1015150188941976670907959)
                ·
                  refine ⟨1522725283412965006361939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015150188941976670907959 1522725283412965006361939)
                  ·
                    refine ⟨2284087925119447509542909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1522725283412965006361939 2284087925119447509542909)
                    ·
                      refine ⟨856532971919792816078591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2284087925119447509542909 856532971919792816078591)
                      ·
                        rfl

theorem cell23_1668092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_1668092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668092 prefixEnd_1668092 := by exact prefixLift 1668092
  have htrace : WordTrace (prefixWord ++ tailWord_1668092) baseStart_1668092 baseEnd_1668092 := by
    simpa [prefixWord, tailWord_1668092, baseEnd_1668092] using wordTrace_append hprefix tailTrace_1668092
  have hstable : (prefixWord ++ tailWord_1668092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668092).length < 2 ^ (prefixWord ++ tailWord_1668092).sum := by decide
  have hdescent : baseEnd_1668092 < baseStart_1668092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668101 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_1668101 : Nat := 118140960795 + 1668101 * 2 ^ 59
def prefixEnd_1668101 : Nat := 4983230072969 + 3 ^ 40 * 1668101 * 2
def baseEnd_1668101 : Nat := 856537593245683280866049

theorem tailTrace_1668101 : CollatzResearch.WordTrace tailWord_1668101 prefixEnd_1668101 856537593245683280866049 := by
  unfold tailWord_1668101
  simp only [CollatzResearch.WordTrace]
  refine ⟨60840641729762440814740157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40560427819841627209826771 60840641729762440814740157)
  ·
    refine ⟨22815240648660915305527559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60840641729762440814740157 22815240648660915305527559)
    ·
      refine ⟨34222860972991372958291339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22815240648660915305527559 34222860972991372958291339)
      ·
        refine ⟨51334291459487059437437009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34222860972991372958291339 51334291459487059437437009)
        ·
          refine ⟨38500718594615294578077757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51334291459487059437437009 38500718594615294578077757)
          ·
            refine ⟨14437769472980735466779159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38500718594615294578077757 14437769472980735466779159)
            ·
              refine ⟨21656654209471103200168739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14437769472980735466779159 21656654209471103200168739)
              ·
                refine ⟨32484981314206654800253109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21656654209471103200168739 32484981314206654800253109)
                ·
                  refine ⟨3045466998206873887523729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32484981314206654800253109 3045466998206873887523729)
                  ·
                    refine ⟨2284100248655155415642797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3045466998206873887523729 2284100248655155415642797)
                    ·
                      refine ⟨856537593245683280866049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2284100248655155415642797 856537593245683280866049)
                      ·
                        rfl

theorem cell23_1668101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_1668101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668101 prefixEnd_1668101 := by exact prefixLift 1668101
  have htrace : WordTrace (prefixWord ++ tailWord_1668101) baseStart_1668101 baseEnd_1668101 := by
    simpa [prefixWord, tailWord_1668101, baseEnd_1668101] using wordTrace_append hprefix tailTrace_1668101
  have hstable : (prefixWord ++ tailWord_1668101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668101).length < 2 ^ (prefixWord ++ tailWord_1668101).sum := by decide
  have hdescent : baseEnd_1668101 < baseStart_1668101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668108 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_1668108 : Nat := 118140960795 + 1668108 * 2 ^ 59
def prefixEnd_1668108 : Nat := 4983230072969 + 3 ^ 40 * 1668108 * 2
def baseEnd_1668108 : Nat := 285513729203421584492839

theorem tailTrace_1668108 : CollatzResearch.WordTrace tailWord_1668108 prefixEnd_1668108 285513729203421584492839 := by
  unfold tailWord_1668108
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420448520368540505122489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40560598027158054006829985 30420448520368540505122489)
  ·
    refine ⟨22815336390276405378841867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30420448520368540505122489 22815336390276405378841867)
    ·
      refine ⟨34223004585414608068262801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22815336390276405378841867 34223004585414608068262801)
      ·
        refine ⟨25667253439060956051197101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34223004585414608068262801 25667253439060956051197101)
        ·
          refine ⟨9625220039647858519198913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25667253439060956051197101 9625220039647858519198913)
          ·
            refine ⟨7218915029735893889399185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9625220039647858519198913 7218915029735893889399185)
            ·
              refine ⟨5414186272301920417049389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7218915029735893889399185 5414186272301920417049389)
              ·
                refine ⟨2030319852113220156393521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5414186272301920417049389 2030319852113220156393521)
                ·
                  refine ⟨1522739889084915117295141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2030319852113220156393521 1522739889084915117295141)
                  ·
                    refine ⟨285513729203421584492839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1522739889084915117295141 285513729203421584492839)
                    ·
                      rfl

theorem cell23_1668108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_1668108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668108 prefixEnd_1668108 := by exact prefixLift 1668108
  have htrace : WordTrace (prefixWord ++ tailWord_1668108) baseStart_1668108 baseEnd_1668108 := by
    simpa [prefixWord, tailWord_1668108, baseEnd_1668108] using wordTrace_append hprefix tailTrace_1668108
  have hstable : (prefixWord ++ tailWord_1668108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668108).length < 2 ^ (prefixWord ++ tailWord_1668108).sum := by decide
  have hdescent : baseEnd_1668108 < baseStart_1668108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668132 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_1668132 : Nat := 118140960795 + 1668132 * 2 ^ 59
def prefixEnd_1668132 : Nat := 4983230072969 + 3 ^ 40 * 1668132 * 2
def baseEnd_1668132 : Nat := 856553511145972659578407

theorem tailTrace_1668132 : CollatzResearch.WordTrace tailWord_1668132 prefixEnd_1668132 856553511145972659578407 := by
  unfold tailWord_1668132
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420886196325066554559325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40561181595100088739412433 30420886196325066554559325)
  ·
    refine ⟨11407832323621899957959747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30420886196325066554559325 11407832323621899957959747)
    ·
      refine ⟨17111748485432849936939621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11407832323621899957959747 17111748485432849936939621)
      ·
        refine ⟨3208452841018659363176179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17111748485432849936939621 3208452841018659363176179)
        ·
          refine ⟨4812679261527989044764269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208452841018659363176179 4812679261527989044764269)
          ·
            refine ⟨1804754723072995891786601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4812679261527989044764269 1804754723072995891786601)
            ·
              refine ⟨1353566042304746918839951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804754723072995891786601 1353566042304746918839951)
              ·
                refine ⟨2030349063457120378259927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353566042304746918839951 2030349063457120378259927)
                ·
                  refine ⟨3045523595185680567389891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030349063457120378259927 3045523595185680567389891)
                  ·
                    refine ⟨4568285392778520851084837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3045523595185680567389891 4568285392778520851084837)
                    ·
                      refine ⟨856553511145972659578407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4568285392778520851084837 856553511145972659578407)
                      ·
                        rfl

theorem cell23_1668132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_1668132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668132 prefixEnd_1668132 := by exact prefixLift 1668132
  have htrace : WordTrace (prefixWord ++ tailWord_1668132) baseStart_1668132 baseEnd_1668132 := by
    simpa [prefixWord, tailWord_1668132, baseEnd_1668132] using wordTrace_append hprefix tailTrace_1668132
  have hstable : (prefixWord ++ tailWord_1668132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668132).length < 2 ^ (prefixWord ++ tailWord_1668132).sum := by decide
  have hdescent : baseEnd_1668132 < baseStart_1668132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668191 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1668191 : Nat := 118140960795 + 1668191 * 2 ^ 59
def prefixEnd_1668191 : Nat := 4983230072969 + 3 ^ 40 * 1668191 * 2
def baseEnd_1668191 : Nat := 856583806504587928740635

theorem tailTrace_1668191 : CollatzResearch.WordTrace tailWord_1668191 prefixEnd_1668191 856583806504587928740635 := by
  unfold tailWord_1668191
  simp only [CollatzResearch.WordTrace]
  refine ⟨60843924299436386185516427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40562616199624257457010951 60843924299436386185516427)
  ·
    refine ⟨91265886449154579278274641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60843924299436386185516427 91265886449154579278274641)
    ·
      refine ⟨68449414836865934458705981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91265886449154579278274641 68449414836865934458705981)
      ·
        refine ⟨25668530563824725422014743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68449414836865934458705981 25668530563824725422014743)
        ·
          refine ⟨38502795845737088133022115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25668530563824725422014743 38502795845737088133022115)
          ·
            refine ⟨57754193768605632199533173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38502795845737088133022115 57754193768605632199533173)
            ·
              refine ⟨5414455665806778018706235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57754193768605632199533173 5414455665806778018706235)
              ·
                refine ⟨8121683498710167028059353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414455665806778018706235 8121683498710167028059353)
                ·
                  refine ⟨6091262624032625271044515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8121683498710167028059353 6091262624032625271044515)
                  ·
                    refine ⟨9136893936048937906566773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6091262624032625271044515 9136893936048937906566773)
                    ·
                      refine ⟨856583806504587928740635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9136893936048937906566773 856583806504587928740635)
                      ·
                        rfl

theorem cell23_1668191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1668191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668191 prefixEnd_1668191 := by exact prefixLift 1668191
  have htrace : WordTrace (prefixWord ++ tailWord_1668191) baseStart_1668191 baseEnd_1668191 := by
    simpa [prefixWord, tailWord_1668191, baseEnd_1668191] using wordTrace_append hprefix tailTrace_1668191
  have hstable : (prefixWord ++ tailWord_1668191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668191).length < 2 ^ (prefixWord ++ tailWord_1668191).sum := by decide
  have hdescent : baseEnd_1668191 < baseStart_1668191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668291 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 4]
def baseStart_1668291 : Nat := 118140960795 + 1668291 * 2 ^ 59
def prefixEnd_1668291 : Nat := 4983230072969 + 3 ^ 40 * 1668291 * 2
def baseEnd_1668291 : Nat := 856635154570037537490175

theorem tailTrace_1668291 : CollatzResearch.WordTrace tailWord_1668291 prefixEnd_1668291 856635154570037537490175 := by
  unfold tailWord_1668291
  simp only [CollatzResearch.WordTrace]
  refine ⟨60847571599074103264156727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40565047732716068842771151 60847571599074103264156727)
  ·
    refine ⟨91271357398611154896235091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60847571599074103264156727 91271357398611154896235091)
    ·
      refine ⟨136907036097916732344352637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91271357398611154896235091 136907036097916732344352637)
      ·
        refine ⟨51340138536718774629132239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136907036097916732344352637 51340138536718774629132239)
        ·
          refine ⟨77010207805078161943698359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51340138536718774629132239 77010207805078161943698359)
          ·
            refine ⟨115515311707617242915547539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77010207805078161943698359 115515311707617242915547539)
            ·
              refine ⟨173272967561425864373321309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115515311707617242915547539 173272967561425864373321309)
              ·
                refine ⟨64977362835534699139995491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173272967561425864373321309 64977362835534699139995491)
                ·
                  refine ⟨97466044253302048709993237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64977362835534699139995491 97466044253302048709993237)
                  ·
                    refine ⟨4568720824373533533280933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97466044253302048709993237 4568720824373533533280933)
                    ·
                      refine ⟨856635154570037537490175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4568720824373533533280933 856635154570037537490175)
                      ·
                        rfl

theorem cell23_1668291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_1668291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668291 prefixEnd_1668291 := by exact prefixLift 1668291
  have htrace : WordTrace (prefixWord ++ tailWord_1668291) baseStart_1668291 baseEnd_1668291 := by
    simpa [prefixWord, tailWord_1668291, baseEnd_1668291] using wordTrace_append hprefix tailTrace_1668291
  have hstable : (prefixWord ++ tailWord_1668291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668291).length < 2 ^ (prefixWord ++ tailWord_1668291).sum := by decide
  have hdescent : baseEnd_1668291 < baseStart_1668291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668292 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1668292 : Nat := 118140960795 + 1668292 * 2 ^ 59
def prefixEnd_1668292 : Nat := 4983230072969 + 3 ^ 40 * 1668292 * 2
def baseEnd_1668292 : Nat := 285545222683564011192557

theorem tailTrace_1668292 : CollatzResearch.WordTrace tailWord_1668292 prefixEnd_1668292 285545222683564011192557 := by
  unfold tailWord_1668292
  simp only [CollatzResearch.WordTrace]
  refine ⟨30423804036035240217471565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40565072048046986956628753 30423804036035240217471565)
  ·
    refine ⟨11408926513513215081551837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30423804036035240217471565 11408926513513215081551837)
    ·
      refine ⟨4278347442567455655581939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11408926513513215081551837 4278347442567455655581939)
      ·
        refine ⟨6417521163851183483372909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4278347442567455655581939 6417521163851183483372909)
        ·
          refine ⟨2406570436444193806264841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6417521163851183483372909 2406570436444193806264841)
          ·
            refine ⟨1804927827333145354698631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2406570436444193806264841 1804927827333145354698631)
            ·
              refine ⟨2707391740999718032047947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804927827333145354698631 2707391740999718032047947)
              ·
                refine ⟨4061087611499577048071921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707391740999718032047947 4061087611499577048071921)
                ·
                  refine ⟨3045815708624682786053941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4061087611499577048071921 3045815708624682786053941)
                  ·
                    refine ⟨285545222683564011192557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3045815708624682786053941 285545222683564011192557)
                    ·
                      rfl

theorem cell23_1668292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1668292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668292 prefixEnd_1668292 := by exact prefixLift 1668292
  have htrace : WordTrace (prefixWord ++ tailWord_1668292) baseStart_1668292 baseEnd_1668292 := by
    simpa [prefixWord, tailWord_1668292, baseEnd_1668292] using wordTrace_append hprefix tailTrace_1668292
  have hstable : (prefixWord ++ tailWord_1668292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668292).length < 2 ^ (prefixWord ++ tailWord_1668292).sum := by decide
  have hdescent : baseEnd_1668292 < baseStart_1668292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668345 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 3]
def baseStart_1668345 : Nat := 118140960795 + 1668345 * 2 ^ 59
def prefixEnd_1668345 : Nat := 4983230072969 + 3 ^ 40 * 1668345 * 2
def baseEnd_1668345 : Nat := 856662882525380326214927

theorem tailTrace_1668345 : CollatzResearch.WordTrace tailWord_1668345 prefixEnd_1668345 856662882525380326214927 := by
  unfold tailWord_1668345
  simp only [CollatzResearch.WordTrace]
  refine ⟨60849541140878470486622489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40566360760585646991081659 60849541140878470486622489)
  ·
    refine ⟨45637155855658852864966867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60849541140878470486622489 45637155855658852864966867)
    ·
      refine ⟨68455733783488279297450301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45637155855658852864966867 68455733783488279297450301)
      ·
        refine ⟨25670900168808104736543863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68455733783488279297450301 25670900168808104736543863)
        ·
          refine ⟨38506350253212157104815795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25670900168808104736543863 38506350253212157104815795)
          ·
            refine ⟨57759525379818235657223693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38506350253212157104815795 57759525379818235657223693)
            ·
              refine ⟨21659822017431838371458885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57759525379818235657223693 21659822017431838371458885)
              ·
                refine ⟨4061216628268469694648541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21659822017431838371458885 4061216628268469694648541)
                ·
                  refine ⟨1522956235600676135493203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4061216628268469694648541 1522956235600676135493203)
                  ·
                    refine ⟨2284434353401014203239805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1522956235600676135493203 2284434353401014203239805)
                    ·
                      refine ⟨856662882525380326214927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2284434353401014203239805 856662882525380326214927)
                      ·
                        rfl

theorem cell23_1668345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_1668345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668345 prefixEnd_1668345 := by exact prefixLift 1668345
  have htrace : WordTrace (prefixWord ++ tailWord_1668345) baseStart_1668345 baseEnd_1668345 := by
    simpa [prefixWord, tailWord_1668345, baseEnd_1668345] using wordTrace_append hprefix tailTrace_1668345
  have hstable : (prefixWord ++ tailWord_1668345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668345).length < 2 ^ (prefixWord ++ tailWord_1668345).sum := by decide
  have hdescent : baseEnd_1668345 < baseStart_1668345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668355 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 1, 5, 2]
def baseStart_1668355 : Nat := 118140960795 + 1668355 * 2 ^ 59
def prefixEnd_1668355 : Nat := 4983230072969 + 3 ^ 40 * 1668355 * 2
def baseEnd_1668355 : Nat := 856668017331925287089881

theorem tailTrace_1668355 : CollatzResearch.WordTrace tailWord_1668355 prefixEnd_1668355 856668017331925287089881 := by
  unfold tailWord_1668355
  simp only [CollatzResearch.WordTrace]
  refine ⟨60849905870842242194486519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40566603913894828129657679 60849905870842242194486519)
  ·
    refine ⟨91274858806263363291729779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60849905870842242194486519 91274858806263363291729779)
    ·
      refine ⟨136912288209395044937594669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91274858806263363291729779 136912288209395044937594669)
      ·
        refine ⟨51342108078523141851598001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136912288209395044937594669 51342108078523141851598001)
        ·
          refine ⟨38506581058892356388698501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51342108078523141851598001 38506581058892356388698501)
          ·
            refine ⟨7219983948542316822880969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38506581058892356388698501 7219983948542316822880969)
            ·
              refine ⟨5414987961406737617160727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7219983948542316822880969 5414987961406737617160727)
              ·
                refine ⟨8122481942110106425741091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414987961406737617160727 8122481942110106425741091)
                ·
                  refine ⟨12183722913165159638611637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122481942110106425741091 12183722913165159638611637)
                  ·
                    refine ⟨1142224023109233716119841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12183722913165159638611637 1142224023109233716119841)
                    ·
                      refine ⟨856668017331925287089881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1142224023109233716119841 856668017331925287089881)
                      ·
                        rfl

theorem cell23_1668355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_1668355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668355 prefixEnd_1668355 := by exact prefixLift 1668355
  have htrace : WordTrace (prefixWord ++ tailWord_1668355) baseStart_1668355 baseEnd_1668355 := by
    simpa [prefixWord, tailWord_1668355, baseEnd_1668355] using wordTrace_append hprefix tailTrace_1668355
  have hstable : (prefixWord ++ tailWord_1668355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668355).length < 2 ^ (prefixWord ++ tailWord_1668355).sum := by decide
  have hdescent : baseEnd_1668355 < baseStart_1668355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668402 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_1668402 : Nat := 118140960795 + 1668402 * 2 ^ 59
def prefixEnd_1668402 : Nat := 4983230072969 + 3 ^ 40 * 1668402 * 2
def baseEnd_1668402 : Nat := 856692150922686603202165

theorem tailTrace_1668402 : CollatzResearch.WordTrace tailWord_1668402 prefixEnd_1668402 856692150922686603202165 := by
  unfold tailWord_1668402
  simp only [CollatzResearch.WordTrace]
  refine ⟨15212905025417992305361865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40567746734447979480964973 15212905025417992305361865)
  ·
    refine ⟨11409678769063494229021399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15212905025417992305361865 11409678769063494229021399)
    ·
      refine ⟨17114518153595241343532099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11409678769063494229021399 17114518153595241343532099)
      ·
        refine ⟨25671777230392862015298149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17114518153595241343532099 25671777230392862015298149)
        ·
          refine ⟨4813458230698661627868403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25671777230392862015298149 4813458230698661627868403)
          ·
            refine ⟨7220187346047992441802605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813458230698661627868403 7220187346047992441802605)
            ·
              refine ⟨2707570254767997165675977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7220187346047992441802605 2707570254767997165675977)
              ·
                refine ⟨2030677691075997874256983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2707570254767997165675977 2030677691075997874256983)
                ·
                  refine ⟨3046016536613996811385475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030677691075997874256983 3046016536613996811385475)
                  ·
                    refine ⟨4569024804920995217078213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3046016536613996811385475 4569024804920995217078213)
                    ·
                      refine ⟨856692150922686603202165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4569024804920995217078213 856692150922686603202165)
                      ·
                        rfl

theorem cell23_1668402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_1668402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668402 prefixEnd_1668402 := by exact prefixLift 1668402
  have htrace : WordTrace (prefixWord ++ tailWord_1668402) baseStart_1668402 baseEnd_1668402 := by
    simpa [prefixWord, tailWord_1668402, baseEnd_1668402] using wordTrace_append hprefix tailTrace_1668402
  have hstable : (prefixWord ++ tailWord_1668402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668402).length < 2 ^ (prefixWord ++ tailWord_1668402).sum := by decide
  have hdescent : baseEnd_1668402 < baseStart_1668402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668415 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_1668415 : Nat := 118140960795 + 1668415 * 2 ^ 59
def prefixEnd_1668415 : Nat := 4983230072969 + 3 ^ 40 * 1668415 * 2
def baseEnd_1668415 : Nat := 856698826171195052339605

theorem tailTrace_1668415 : CollatzResearch.WordTrace tailWord_1668415 prefixEnd_1668415 856698826171195052339605 := by
  unfold tailWord_1668415
  simp only [CollatzResearch.WordTrace]
  refine ⟨60852094250624872441670699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40568062833749914961113799 60852094250624872441670699)
  ·
    refine ⟨91278141375937308662506049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60852094250624872441670699 91278141375937308662506049)
    ·
      refine ⟨68458606031952981496879537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91278141375937308662506049 68458606031952981496879537)
      ·
        refine ⟨51343954523964736122659653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68458606031952981496879537 51343954523964736122659653)
        ·
          refine ⟨9626991473243388022998685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51343954523964736122659653 9626991473243388022998685)
          ·
            refine ⟨3610121802466270508624507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9626991473243388022998685 3610121802466270508624507)
            ·
              refine ⟨5415182703699405762936761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610121802466270508624507 5415182703699405762936761)
              ·
                refine ⟨4061387027774554322202571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5415182703699405762936761 4061387027774554322202571)
                ·
                  refine ⟨6092080541661831483303857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4061387027774554322202571 6092080541661831483303857)
                  ·
                    refine ⟨4569060406246373612477893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6092080541661831483303857 4569060406246373612477893)
                    ·
                      refine ⟨856698826171195052339605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4569060406246373612477893 856698826171195052339605)
                      ·
                        rfl

theorem cell23_1668415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_1668415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668415 prefixEnd_1668415 := by exact prefixLift 1668415
  have htrace : WordTrace (prefixWord ++ tailWord_1668415) baseStart_1668415 baseEnd_1668415 := by
    simpa [prefixWord, tailWord_1668415, baseEnd_1668415] using wordTrace_append hprefix tailTrace_1668415
  have hstable : (prefixWord ++ tailWord_1668415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668415).length < 2 ^ (prefixWord ++ tailWord_1668415).sum := by decide
  have hdescent : baseEnd_1668415 < baseStart_1668415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668419 : List Nat := [1, 1, 1, 3, 1, 3, 1, 7, 1, 2, 2]
def baseStart_1668419 : Nat := 118140960795 + 1668419 * 2 ^ 59
def prefixEnd_1668419 : Nat := 4983230072969 + 3 ^ 40 * 1668419 * 2
def baseEnd_1668419 : Nat := 856700880093813036689587

theorem tailTrace_1668419 : CollatzResearch.WordTrace tailWord_1668419 prefixEnd_1668419 856700880093813036689587 := by
  unfold tailWord_1668419
  simp only [CollatzResearch.WordTrace]
  refine ⟨60852240142610381124816311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40568160095073587416544207 60852240142610381124816311)
  ·
    refine ⟨91278360213915571687224467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60852240142610381124816311 91278360213915571687224467)
    ·
      refine ⟨136917540320873357530836701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91278360213915571687224467 136917540320873357530836701)
      ·
        refine ⟨51344077620327509074063763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136917540320873357530836701 51344077620327509074063763)
        ·
          refine ⟨77016116430491263611095645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51344077620327509074063763 77016116430491263611095645)
          ·
            refine ⟨28881043661434223854160867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77016116430491263611095645 28881043661434223854160867)
            ·
              refine ⟨43321565492151335781241301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28881043661434223854160867 43321565492151335781241301)
              ·
                refine ⟨1015349191222296932372843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43321565492151335781241301 1015349191222296932372843)
                ·
                  refine ⟨1523023786833445398559265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015349191222296932372843 1523023786833445398559265)
                  ·
                    refine ⟨1142267840125084048919449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1523023786833445398559265 1142267840125084048919449)
                    ·
                      refine ⟨856700880093813036689587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1142267840125084048919449 856700880093813036689587)
                      ·
                        rfl

theorem cell23_1668419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 2, 2].length) (baseStart_1668419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668419 prefixEnd_1668419 := by exact prefixLift 1668419
  have htrace : WordTrace (prefixWord ++ tailWord_1668419) baseStart_1668419 baseEnd_1668419 := by
    simpa [prefixWord, tailWord_1668419, baseEnd_1668419] using wordTrace_append hprefix tailTrace_1668419
  have hstable : (prefixWord ++ tailWord_1668419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668419).length < 2 ^ (prefixWord ++ tailWord_1668419).sum := by decide
  have hdescent : baseEnd_1668419 < baseStart_1668419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668436 : List Nat := [2, 4, 1, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_1668436 : Nat := 118140960795 + 1668436 * 2 ^ 59
def prefixEnd_1668436 : Nat := 4983230072969 + 3 ^ 40 * 1668436 * 2
def baseEnd_1668436 : Nat := 856709609264939470177009

theorem tailTrace_1668436 : CollatzResearch.WordTrace tailWord_1668436 prefixEnd_1668436 856709609264939470177009 := by
  unfold tailWord_1668436
  simp only [CollatzResearch.WordTrace]
  refine ⟨30426430091774396514092581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40568573455699195352123441 30426430091774396514092581)
  ·
    refine ⟨5704955642207699346392359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30426430091774396514092581 5704955642207699346392359)
    ·
      refine ⟨8557433463311549019588539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5704955642207699346392359 8557433463311549019588539)
      ·
        refine ⟨12836150194967323529382809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8557433463311549019588539 12836150194967323529382809)
        ·
          refine ⟨9627112646225492647037107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12836150194967323529382809 9627112646225492647037107)
          ·
            refine ⟨14440668969338238970555661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9627112646225492647037107 14440668969338238970555661)
            ·
              refine ⟨5415250863501839613958373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14440668969338238970555661 5415250863501839613958373)
              ·
                refine ⟨1015359536906594927617195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5415250863501839613958373 1015359536906594927617195)
                ·
                  refine ⟨1523039305359892391425793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015359536906594927617195 1523039305359892391425793)
                  ·
                    refine ⟨1142279479019919293569345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1523039305359892391425793 1142279479019919293569345)
                    ·
                      refine ⟨856709609264939470177009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1142279479019919293569345 856709609264939470177009)
                      ·
                        rfl

theorem cell23_1668436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_1668436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668436 prefixEnd_1668436 := by exact prefixLift 1668436
  have htrace : WordTrace (prefixWord ++ tailWord_1668436) baseStart_1668436 baseEnd_1668436 := by
    simpa [prefixWord, tailWord_1668436, baseEnd_1668436] using wordTrace_append hprefix tailTrace_1668436
  have hstable : (prefixWord ++ tailWord_1668436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668436).length < 2 ^ (prefixWord ++ tailWord_1668436).sum := by decide
  have hdescent : baseEnd_1668436 < baseStart_1668436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668452 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_1668452 : Nat := 118140960795 + 1668452 * 2 ^ 59
def prefixEnd_1668452 : Nat := 4983230072969 + 3 ^ 40 * 1668452 * 2
def baseEnd_1668452 : Nat := 856717824955411407576935

theorem tailTrace_1668452 : CollatzResearch.WordTrace tailWord_1668452 prefixEnd_1668452 856717824955411407576935 := by
  unfold tailWord_1668452
  simp only [CollatzResearch.WordTrace]
  refine ⟨30426721875745413880383805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40568962500993885173845073 30426721875745413880383805)
  ·
    refine ⟨11410020703404530205143927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30426721875745413880383805 11410020703404530205143927)
    ·
      refine ⟨17115031055106795307715891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11410020703404530205143927 17115031055106795307715891)
      ·
        refine ⟨25672546582660192961573837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17115031055106795307715891 25672546582660192961573837)
        ·
          refine ⟨9627204968497572360590189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25672546582660192961573837 9627204968497572360590189)
          ·
            refine ⟨3610201863186589635221321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9627204968497572360590189 3610201863186589635221321)
            ·
              refine ⟨2707651397389942226415991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3610201863186589635221321 2707651397389942226415991)
              ·
                refine ⟨4061477096084913339623987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707651397389942226415991 4061477096084913339623987)
                ·
                  refine ⟨6092215644127370009435981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4061477096084913339623987 6092215644127370009435981)
                  ·
                    refine ⟨2284580866547763753538493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6092215644127370009435981 2284580866547763753538493)
                    ·
                      refine ⟨856717824955411407576935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2284580866547763753538493 856717824955411407576935)
                      ·
                        rfl

theorem cell23_1668452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_1668452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668452 prefixEnd_1668452 := by exact prefixLift 1668452
  have htrace : WordTrace (prefixWord ++ tailWord_1668452) baseStart_1668452 baseEnd_1668452 := by
    simpa [prefixWord, tailWord_1668452, baseEnd_1668452] using wordTrace_append hprefix tailTrace_1668452
  have hstable : (prefixWord ++ tailWord_1668452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668452).length < 2 ^ (prefixWord ++ tailWord_1668452).sum := by decide
  have hdescent : baseEnd_1668452 < baseStart_1668452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668505 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_1668505 : Nat := 118140960795 + 1668505 * 2 ^ 59
def prefixEnd_1668505 : Nat := 4983230072969 + 3 ^ 40 * 1668505 * 2
def baseEnd_1668505 : Nat := 856745039430099700214191

theorem tailTrace_1668505 : CollatzResearch.WordTrace tailWord_1668505 prefixEnd_1668505 856745039430099700214191 := by
  unfold tailWord_1668505
  simp only [CollatzResearch.WordTrace]
  refine ⟨60855376820298817812446969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40570251213532545208297979 60855376820298817812446969)
  ·
    refine ⟨45641532615224113359335227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60855376820298817812446969 45641532615224113359335227)
    ·
      refine ⟨68462298922836170039002841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45641532615224113359335227 68462298922836170039002841)
      ·
        refine ⟨51346724192127127529252131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68462298922836170039002841 51346724192127127529252131)
        ·
          refine ⟨77020086288190691293878197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51346724192127127529252131 77020086288190691293878197)
          ·
            refine ⟨7220633089517877308801081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77020086288190691293878197 7220633089517877308801081)
            ·
              refine ⟨5415474817138407981600811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7220633089517877308801081 5415474817138407981600811)
              ·
                refine ⟨8123212225707611972401217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415474817138407981600811 8123212225707611972401217)
                ·
                  refine ⟨6092409169280708979300913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8123212225707611972401217 6092409169280708979300913)
                  ·
                    refine ⟨4569306876960531734475685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6092409169280708979300913 4569306876960531734475685)
                    ·
                      refine ⟨856745039430099700214191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4569306876960531734475685 856745039430099700214191)
                      ·
                        rfl

theorem cell23_1668505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_1668505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668505 prefixEnd_1668505 := by exact prefixLift 1668505
  have htrace : WordTrace (prefixWord ++ tailWord_1668505) baseStart_1668505 baseEnd_1668505 := by
    simpa [prefixWord, tailWord_1668505, baseEnd_1668505] using wordTrace_append hprefix tailTrace_1668505
  have hstable : (prefixWord ++ tailWord_1668505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668505).length < 2 ^ (prefixWord ++ tailWord_1668505).sum := by decide
  have hdescent : baseEnd_1668505 < baseStart_1668505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668509 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_1668509 : Nat := 118140960795 + 1668509 * 2 ^ 59
def prefixEnd_1668509 : Nat := 4983230072969 + 3 ^ 40 * 1668509 * 2
def baseEnd_1668509 : Nat := 856747093352717684564173

theorem tailTrace_1668509 : CollatzResearch.WordTrace tailWord_1668509 prefixEnd_1668509 856747093352717684564173 := by
  unfold tailWord_1668509
  simp only [CollatzResearch.WordTrace]
  refine ⟨60855522712284326495592581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40570348474856217663728387 60855522712284326495592581)
  ·
    refine ⟨11410410508553311217923609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60855522712284326495592581 11410410508553311217923609)
    ·
      refine ⟨8557807881414983413442707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11410410508553311217923609 8557807881414983413442707)
      ·
        refine ⟨12836711822122475120164061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8557807881414983413442707 12836711822122475120164061)
        ·
          refine ⟨4813766933295928170061523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12836711822122475120164061 4813766933295928170061523)
          ·
            refine ⟨7220650399943892255092285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813766933295928170061523 7220650399943892255092285)
            ·
              refine ⟨2707743899978959595659607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7220650399943892255092285 2707743899978959595659607)
              ·
                refine ⟨4061615849968439393489411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707743899978959595659607 4061615849968439393489411)
                ·
                  refine ⟨6092423774952659090234117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4061615849968439393489411 6092423774952659090234117)
                  ·
                    refine ⟨1142329457803623579418897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6092423774952659090234117 1142329457803623579418897)
                    ·
                      refine ⟨856747093352717684564173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1142329457803623579418897 856747093352717684564173)
                      ·
                        rfl

theorem cell23_1668509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_1668509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668509 prefixEnd_1668509 := by exact prefixLift 1668509
  have htrace : WordTrace (prefixWord ++ tailWord_1668509) baseStart_1668509 baseEnd_1668509 := by
    simpa [prefixWord, tailWord_1668509, baseEnd_1668509] using wordTrace_append hprefix tailTrace_1668509
  have hstable : (prefixWord ++ tailWord_1668509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668509).length < 2 ^ (prefixWord ++ tailWord_1668509).sum := by decide
  have hdescent : baseEnd_1668509 < baseStart_1668509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668552 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_1668552 : Nat := 118140960795 + 1668552 * 2 ^ 59
def prefixEnd_1668552 : Nat := 4983230072969 + 3 ^ 40 * 1668552 * 2
def baseEnd_1668552 : Nat := 856769173020861016326475

theorem tailTrace_1668552 : CollatzResearch.WordTrace tailWord_1668552 prefixEnd_1668552 856769173020861016326475 := by
  unfold tailWord_1668552
  simp only [CollatzResearch.WordTrace]
  refine ⟨30428545525564272419703955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40571394034085696559605273 30428545525564272419703955)
  ·
    refine ⟨45642818288346408629555933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30428545525564272419703955 45642818288346408629555933)
    ·
      refine ⟨17116056858129903236083475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45642818288346408629555933 17116056858129903236083475)
      ·
        refine ⟨25674085287194854854125213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17116056858129903236083475 25674085287194854854125213)
        ·
          refine ⟨9627781982698070570296955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25674085287194854854125213 9627781982698070570296955)
          ·
            refine ⟨14441672974047105855445433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9627781982698070570296955 14441672974047105855445433)
            ·
              refine ⟨10831254730535329391584075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14441672974047105855445433 10831254730535329391584075)
              ·
                refine ⟨16246882095802994087376113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10831254730535329391584075 16246882095802994087376113)
                ·
                  refine ⟨12185161571852245565532085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16246882095802994087376113 12185161571852245565532085)
                  ·
                    refine ⟨1142358897361148021768633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12185161571852245565532085 1142358897361148021768633)
                    ·
                      refine ⟨856769173020861016326475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1142358897361148021768633 856769173020861016326475)
                      ·
                        rfl

theorem cell23_1668552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_1668552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668552 prefixEnd_1668552 := by exact prefixLift 1668552
  have htrace : WordTrace (prefixWord ++ tailWord_1668552) baseStart_1668552 baseEnd_1668552 := by
    simpa [prefixWord, tailWord_1668552, baseEnd_1668552] using wordTrace_append hprefix tailTrace_1668552
  have hstable : (prefixWord ++ tailWord_1668552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668552).length < 2 ^ (prefixWord ++ tailWord_1668552).sum := by decide
  have hdescent : baseEnd_1668552 < baseStart_1668552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668585 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 3]
def baseStart_1668585 : Nat := 118140960795 + 1668585 * 2 ^ 59
def prefixEnd_1668585 : Nat := 4983230072969 + 3 ^ 40 * 1668585 * 2
def baseEnd_1668585 : Nat := 856786117882459387213823

theorem tailTrace_1668585 : CollatzResearch.WordTrace tailWord_1668585 prefixEnd_1668585 856786117882459387213823 := by
  unfold tailWord_1668585
  simp only [CollatzResearch.WordTrace]
  refine ⟨60858294660008991475359209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40572196440005994316906139 60858294660008991475359209)
  ·
    refine ⟨45643720995006743606519407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60858294660008991475359209 45643720995006743606519407)
    ·
      refine ⟨68465581492510115409779111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45643720995006743606519407 68465581492510115409779111)
      ·
        refine ⟨102698372238765173114668667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68465581492510115409779111 102698372238765173114668667)
        ·
          refine ⟨154047558358147759672003001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102698372238765173114668667 154047558358147759672003001)
          ·
            refine ⟨115535668768610819754002251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154047558358147759672003001 115535668768610819754002251)
            ·
              refine ⟨173303503152916229631003377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115535668768610819754002251 173303503152916229631003377)
              ·
                refine ⟨129977627364687172223252533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173303503152916229631003377 129977627364687172223252533)
                ·
                  refine ⟨12185402565439422395929925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129977627364687172223252533 12185402565439422395929925)
                  ·
                    refine ⟨2284762981019891699236861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12185402565439422395929925 2284762981019891699236861)
                    ·
                      refine ⟨856786117882459387213823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2284762981019891699236861 856786117882459387213823)
                      ·
                        rfl

theorem cell23_1668585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_1668585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668585 prefixEnd_1668585 := by exact prefixLift 1668585
  have htrace : WordTrace (prefixWord ++ tailWord_1668585) baseStart_1668585 baseEnd_1668585 := by
    simpa [prefixWord, tailWord_1668585, baseEnd_1668585] using wordTrace_append hprefix tailTrace_1668585
  have hstable : (prefixWord ++ tailWord_1668585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668585).length < 2 ^ (prefixWord ++ tailWord_1668585).sum := by decide
  have hdescent : baseEnd_1668585 < baseStart_1668585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668602 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_1668602 : Nat := 118140960795 + 1668602 * 2 ^ 59
def prefixEnd_1668602 : Nat := 4983230072969 + 3 ^ 40 * 1668602 * 2
def baseEnd_1668602 : Nat := 856794847053585820701245

theorem tailTrace_1668602 : CollatzResearch.WordTrace tailWord_1668602 prefixEnd_1668602 856794847053585820701245 := by
  unfold tailWord_1668602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15214728675236850844682015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40572609800631602252485373 15214728675236850844682015)
  ·
    refine ⟨22822093012855276267023023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15214728675236850844682015 22822093012855276267023023)
    ·
      refine ⟨34233139519282914400534535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22822093012855276267023023 34233139519282914400534535)
      ·
        refine ⟨51349709278924371600801803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34233139519282914400534535 51349709278924371600801803)
        ·
          refine ⟨77024563918386557401202705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51349709278924371600801803 77024563918386557401202705)
          ·
            refine ⟨57768422938789918050902029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77024563918386557401202705 57768422938789918050902029)
            ·
              refine ⟨21663158602046219269088261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57768422938789918050902029 21663158602046219269088261)
              ·
                refine ⟨4061842237883666112954049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21663158602046219269088261 4061842237883666112954049)
                ·
                  refine ⟨3046381678412749584715537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4061842237883666112954049 3046381678412749584715537)
                  ·
                    refine ⟨2284786258809562188536653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3046381678412749584715537 2284786258809562188536653)
                    ·
                      refine ⟨856794847053585820701245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2284786258809562188536653 856794847053585820701245)
                      ·
                        rfl

theorem cell23_1668602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_1668602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668602 prefixEnd_1668602 := by exact prefixLift 1668602
  have htrace : WordTrace (prefixWord ++ tailWord_1668602) baseStart_1668602 baseEnd_1668602 := by
    simpa [prefixWord, tailWord_1668602, baseEnd_1668602] using wordTrace_append hprefix tailTrace_1668602
  have hstable : (prefixWord ++ tailWord_1668602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668602).length < 2 ^ (prefixWord ++ tailWord_1668602).sum := by decide
  have hdescent : baseEnd_1668602 < baseStart_1668602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668645 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_1668645 : Nat := 118140960795 + 1668645 * 2 ^ 59
def prefixEnd_1668645 : Nat := 4983230072969 + 3 ^ 40 * 1668645 * 2
def baseEnd_1668645 : Nat := 856816926721729152463547

theorem tailTrace_1668645 : CollatzResearch.WordTrace tailWord_1668645 prefixEnd_1668645 856816926721729152463547 := by
  unfold tailWord_1668645
  simp only [CollatzResearch.WordTrace]
  refine ⟨60860483039791621722543389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40573655359861081148362259 60860483039791621722543389)
  ·
    refine ⟨22822681139921858145953771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60860483039791621722543389 22822681139921858145953771)
    ·
      refine ⟨34234021709882787218930657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22822681139921858145953771 34234021709882787218930657)
      ·
        refine ⟨25675516282412090414197993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34234021709882787218930657 25675516282412090414197993)
        ·
          refine ⟨19256637211809067810648495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25675516282412090414197993 19256637211809067810648495)
          ·
            refine ⟨28884955817713601715972743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19256637211809067810648495 28884955817713601715972743)
            ·
              refine ⟨43327433726570402573959115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28884955817713601715972743 43327433726570402573959115)
              ·
                refine ⟨64991150589855603860938673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43327433726570402573959115 64991150589855603860938673)
                ·
                  refine ⟨48743362942391702895704005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64991150589855603860938673 48743362942391702895704005)
                  ·
                    refine ⟨9139380551698444292944501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48743362942391702895704005 9139380551698444292944501)
                    ·
                      refine ⟨856816926721729152463547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9139380551698444292944501 856816926721729152463547)
                      ·
                        rfl

theorem cell23_1668645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_1668645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668645 prefixEnd_1668645 := by exact prefixLift 1668645
  have htrace : WordTrace (prefixWord ++ tailWord_1668645) baseStart_1668645 baseEnd_1668645 := by
    simpa [prefixWord, tailWord_1668645, baseEnd_1668645] using wordTrace_append hprefix tailTrace_1668645
  have hstable : (prefixWord ++ tailWord_1668645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668645).length < 2 ^ (prefixWord ++ tailWord_1668645).sum := by decide
  have hdescent : baseEnd_1668645 < baseStart_1668645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668666 : List Nat := [3, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3]
def baseStart_1668666 : Nat := 118140960795 + 1668666 * 2 ^ 59
def prefixEnd_1668666 : Nat := 4983230072969 + 3 ^ 40 * 1668666 * 2
def baseEnd_1668666 : Nat := 856827709815473570300951

theorem tailTrace_1668666 : CollatzResearch.WordTrace tailWord_1668666 prefixEnd_1668666 856827709815473570300951 := by
  unfold tailWord_1668666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15215312243178885577264463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40574165981810361539371901 15215312243178885577264463)
  ·
    refine ⟨22822968364768328365896695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15215312243178885577264463 22822968364768328365896695)
    ·
      refine ⟨34234452547152492548845043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22822968364768328365896695 34234452547152492548845043)
      ·
        refine ⟨51351678820728738823267565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34234452547152492548845043 51351678820728738823267565)
        ·
          refine ⟨19256879557773277058725337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51351678820728738823267565 19256879557773277058725337)
          ·
            refine ⟨14442659668329957794044003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19256879557773277058725337 14442659668329957794044003)
            ·
              refine ⟨21663989502494936691066005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14442659668329957794044003 21663989502494936691066005)
              ·
                refine ⟨1015499507929450157393719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21663989502494936691066005 1015499507929450157393719)
                ·
                  refine ⟨1523249261894175236090579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015499507929450157393719 1523249261894175236090579)
                  ·
                    refine ⟨2284873892841262854135869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1523249261894175236090579 2284873892841262854135869)
                    ·
                      refine ⟨856827709815473570300951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2284873892841262854135869 856827709815473570300951)
                      ·
                        rfl

theorem cell23_1668666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3].length) (baseStart_1668666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668666 prefixEnd_1668666 := by exact prefixLift 1668666
  have htrace : WordTrace (prefixWord ++ tailWord_1668666) baseStart_1668666 baseEnd_1668666 := by
    simpa [prefixWord, tailWord_1668666, baseEnd_1668666] using wordTrace_append hprefix tailTrace_1668666
  have hstable : (prefixWord ++ tailWord_1668666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668666).length < 2 ^ (prefixWord ++ tailWord_1668666).sum := by decide
  have hdescent : baseEnd_1668666 < baseStart_1668666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668689 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 4]
def baseStart_1668689 : Nat := 118140960795 + 1668689 * 2 ^ 59
def prefixEnd_1668689 : Nat := 4983230072969 + 3 ^ 40 * 1668689 * 2
def baseEnd_1668689 : Nat := 856839519870526980313345

theorem tailTrace_1668689 : CollatzResearch.WordTrace tailWord_1668689 prefixEnd_1668689 856839519870526980313345 := by
  unfold tailWord_1668689
  simp only [CollatzResearch.WordTrace]
  refine ⟨60862087851632217237145121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40574725234421478158096747 60862087851632217237145121)
  ·
    refine ⟨45646565888724162927858841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60862087851632217237145121 45646565888724162927858841)
    ·
      refine ⟨34234924416543122195894131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45646565888724162927858841 34234924416543122195894131)
      ·
        refine ⟨51352386624814683293841197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34234924416543122195894131 51352386624814683293841197)
        ·
          refine ⟨19257144984305506235190449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51352386624814683293841197 19257144984305506235190449)
          ·
            refine ⟨14442858738229129676392837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19257144984305506235190449 14442858738229129676392837)
            ·
              refine ⟨2708036013417961814323657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14442858738229129676392837 2708036013417961814323657)
              ·
                refine ⟨2031027010063471360742743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2708036013417961814323657 2031027010063471360742743)
                ·
                  refine ⟨3046540515095207041114115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031027010063471360742743 3046540515095207041114115)
                  ·
                    refine ⟨4569810772642810561671173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3046540515095207041114115 4569810772642810561671173)
                    ·
                      refine ⟨856839519870526980313345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4569810772642810561671173 856839519870526980313345)
                      ·
                        rfl

theorem cell23_1668689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_1668689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668689 prefixEnd_1668689 := by exact prefixLift 1668689
  have htrace : WordTrace (prefixWord ++ tailWord_1668689) baseStart_1668689 baseEnd_1668689 := by
    simpa [prefixWord, tailWord_1668689, baseEnd_1668689] using wordTrace_append hprefix tailTrace_1668689
  have hstable : (prefixWord ++ tailWord_1668689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668689).length < 2 ^ (prefixWord ++ tailWord_1668689).sum := by decide
  have hdescent : baseEnd_1668689 < baseStart_1668689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668692 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1668692 : Nat := 118140960795 + 1668692 * 2 ^ 59
def prefixEnd_1668692 : Nat := 4983230072969 + 3 ^ 40 * 1668692 * 2
def baseEnd_1668692 : Nat := 856841060312490468575831

theorem tailTrace_1668692 : CollatzResearch.WordTrace tailWord_1668692 prefixEnd_1668692 856841060312490468575831 := by
  unfold tailWord_1668692
  simp only [CollatzResearch.WordTrace]
  refine ⟨30431098635310674374752165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40574798180414232499669553 30431098635310674374752165)
  ·
    refine ⟨5705830994120751445266031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30431098635310674374752165 5705830994120751445266031)
    ·
      refine ⟨8558746491181127167899047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5705830994120751445266031 8558746491181127167899047)
      ·
        refine ⟨12838119736771690751848571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8558746491181127167899047 12838119736771690751848571)
        ·
          refine ⟨19257179605157536127772857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12838119736771690751848571 19257179605157536127772857)
          ·
            refine ⟨14442884703868152095829643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19257179605157536127772857 14442884703868152095829643)
            ·
              refine ⟨21664327055802228143744465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14442884703868152095829643 21664327055802228143744465)
              ·
                refine ⟨16248245291851671107808349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21664327055802228143744465 16248245291851671107808349)
                ·
                  refine ⟨6093091984444376665428131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16248245291851671107808349 6093091984444376665428131)
                  ·
                    refine ⟨9139637976666564998142197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6093091984444376665428131 9139637976666564998142197)
                    ·
                      refine ⟨856841060312490468575831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9139637976666564998142197 856841060312490468575831)
                      ·
                        rfl

theorem cell23_1668692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1668692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668692 prefixEnd_1668692 := by exact prefixLift 1668692
  have htrace : WordTrace (prefixWord ++ tailWord_1668692) baseStart_1668692 baseEnd_1668692 := by
    simpa [prefixWord, tailWord_1668692, baseEnd_1668692] using wordTrace_append hprefix tailTrace_1668692
  have hstable : (prefixWord ++ tailWord_1668692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668692).length < 2 ^ (prefixWord ++ tailWord_1668692).sum := by decide
  have hdescent : baseEnd_1668692 < baseStart_1668692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668694 : List Nat := [5, 2, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1668694 : Nat := 118140960795 + 1668694 * 2 ^ 59
def prefixEnd_1668694 : Nat := 4983230072969 + 3 ^ 40 * 1668694 * 2
def baseEnd_1668694 : Nat := 285614029091266486916941

theorem tailTrace_1668694 : CollatzResearch.WordTrace tailWord_1668694 prefixEnd_1668694 285614029091266486916941 := by
  unfold tailWord_1668694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803891888538381443192321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40574846811076068727384757 3803891888538381443192321)
  ·
    refine ⟨2852918916403786082394241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3803891888538381443192321 2852918916403786082394241)
    ·
      refine ⟨2139689187302839561795681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2852918916403786082394241 2139689187302839561795681)
      ·
        refine ⟨1604766890477129671346761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2139689187302839561795681 1604766890477129671346761)
        ·
          refine ⟨1203575167857847253510071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604766890477129671346761 1203575167857847253510071)
          ·
            refine ⟨1805362751786770880265107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203575167857847253510071 1805362751786770880265107)
            ·
              refine ⟨2708044127680156320397661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805362751786770880265107 2708044127680156320397661)
              ·
                refine ⟨1015516547880058620149123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2708044127680156320397661 1015516547880058620149123)
                ·
                  refine ⟨1523274821820087930223685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015516547880058620149123 1523274821820087930223685)
                  ·
                    refine ⟨285614029091266486916941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1523274821820087930223685 285614029091266486916941)
                    ·
                      rfl

theorem cell23_1668694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1668694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668694 prefixEnd_1668694 := by exact prefixLift 1668694
  have htrace : WordTrace (prefixWord ++ tailWord_1668694) baseStart_1668694 baseEnd_1668694 := by
    simpa [prefixWord, tailWord_1668694, baseEnd_1668694] using wordTrace_append hprefix tailTrace_1668694
  have hstable : (prefixWord ++ tailWord_1668694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668694).length < 2 ^ (prefixWord ++ tailWord_1668694).sum := by decide
  have hdescent : baseEnd_1668694 < baseStart_1668694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668700 : List Nat := [2, 2, 4, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_1668700 : Nat := 118140960795 + 1668700 * 2 ^ 59
def prefixEnd_1668700 : Nat := 4983230072969 + 3 ^ 40 * 1668700 * 2
def baseEnd_1668700 : Nat := 856845168157726437275795

theorem tailTrace_1668700 : CollatzResearch.WordTrace tailWord_1668700 prefixEnd_1668700 856845168157726437275795 := by
  unfold tailWord_1668700
  simp only [CollatzResearch.WordTrace]
  refine ⟨30431244527296183057897777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40574992703061577410530369 30431244527296183057897777)
  ·
    refine ⟨22823433395472137293423333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30431244527296183057897777 22823433395472137293423333)
    ·
      refine ⟨4279393761651025742516875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22823433395472137293423333 4279393761651025742516875)
      ·
        refine ⟨6419090642476538613775313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279393761651025742516875 6419090642476538613775313)
        ·
          refine ⟨4814317981857403960331485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6419090642476538613775313 4814317981857403960331485)
          ·
            refine ⟨1805369243196526485124307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4814317981857403960331485 1805369243196526485124307)
            ·
              refine ⟨2708053864794789727686461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805369243196526485124307 2708053864794789727686461)
              ·
                refine ⟨1015520199298046147882423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2708053864794789727686461 1015520199298046147882423)
                ·
                  refine ⟨1523280298947069221823635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015520199298046147882423 1523280298947069221823635)
                  ·
                    refine ⟨2284920448420603832735453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1523280298947069221823635 2284920448420603832735453)
                    ·
                      refine ⟨856845168157726437275795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2284920448420603832735453 856845168157726437275795)
                      ·
                        rfl

theorem cell23_1668700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_1668700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668700 prefixEnd_1668700 := by exact prefixLift 1668700
  have htrace : WordTrace (prefixWord ++ tailWord_1668700) baseStart_1668700 baseEnd_1668700 := by
    simpa [prefixWord, tailWord_1668700, baseEnd_1668700] using wordTrace_append hprefix tailTrace_1668700
  have hstable : (prefixWord ++ tailWord_1668700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668700).length < 2 ^ (prefixWord ++ tailWord_1668700).sum := by decide
  have hdescent : baseEnd_1668700 < baseStart_1668700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668709 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_1668709 : Nat := 118140960795 + 1668709 * 2 ^ 59
def prefixEnd_1668709 : Nat := 4983230072969 + 3 ^ 40 * 1668709 * 2
def baseEnd_1668709 : Nat := 856849789483616902063253

theorem tailTrace_1668709 : CollatzResearch.WordTrace tailWord_1668709 prefixEnd_1668709 856849789483616902063253 := by
  unfold tailWord_1668709
  simp only [CollatzResearch.WordTrace]
  refine ⟨60862817311559760652873181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40575211541039840435248787 60862817311559760652873181)
  ·
    refine ⟨22823556491834910244827443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60862817311559760652873181 22823556491834910244827443)
    ·
      refine ⟨34235334737752365367241165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22823556491834910244827443 34235334737752365367241165)
      ·
        refine ⟨12838250526657137012715437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34235334737752365367241165 12838250526657137012715437)
        ·
          refine ⟨4814343947496426379768289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12838250526657137012715437 4814343947496426379768289)
          ·
            refine ⟨3610757960622319784826217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4814343947496426379768289 3610757960622319784826217)
            ·
              refine ⟨2708068470466739838619663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3610757960622319784826217 2708068470466739838619663)
              ·
                refine ⟨4062102705700109757929495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708068470466739838619663 4062102705700109757929495)
                ·
                  refine ⟨6093154058550164636894243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062102705700109757929495 6093154058550164636894243)
                  ·
                    refine ⟨9139731087825246955341365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6093154058550164636894243 9139731087825246955341365)
                    ·
                      refine ⟨856849789483616902063253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9139731087825246955341365 856849789483616902063253)
                      ·
                        rfl

theorem cell23_1668709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_1668709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668709 prefixEnd_1668709 := by exact prefixLift 1668709
  have htrace : WordTrace (prefixWord ++ tailWord_1668709) baseStart_1668709 baseEnd_1668709 := by
    simpa [prefixWord, tailWord_1668709, baseEnd_1668709] using wordTrace_append hprefix tailTrace_1668709
  have hstable : (prefixWord ++ tailWord_1668709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668709).length < 2 ^ (prefixWord ++ tailWord_1668709).sum := by decide
  have hdescent : baseEnd_1668709 < baseStart_1668709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668712 : List Nat := [2, 1, 4, 3, 1, 1, 11]
def baseStart_1668712 : Nat := 118140960795 + 1668712 * 2 ^ 59
def prefixEnd_1668712 : Nat := 4983230072969 + 3 ^ 40 * 1668712 * 2
def baseEnd_1668712 : Nat := 10578411480562720868219

theorem tailTrace_1668712 : CollatzResearch.WordTrace tailWord_1668712 prefixEnd_1668712 10578411480562720868219 := by
  unfold tailWord_1668712
  simp only [CollatzResearch.WordTrace]
  refine ⟨30431463365274446082616195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40575284487032594776821593 30431463365274446082616195)
  ·
    refine ⟨45647195047911669123924293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30431463365274446082616195 45647195047911669123924293)
    ·
      refine ⟨8558849071483437960735805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45647195047911669123924293 8558849071483437960735805)
      ·
        refine ⟨3209568401806289235275927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8558849071483437960735805 3209568401806289235275927)
        ·
          refine ⟨4814352602709433852913891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209568401806289235275927 4814352602709433852913891)
          ·
            refine ⟨7221528904064150779370837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814352602709433852913891 7221528904064150779370837)
            ·
              refine ⟨10578411480562720868219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7221528904064150779370837 10578411480562720868219)
              ·
                rfl

theorem cell23_1668712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 11].length) (baseStart_1668712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668712 prefixEnd_1668712 := by exact prefixLift 1668712
  have htrace : WordTrace (prefixWord ++ tailWord_1668712) baseStart_1668712 baseEnd_1668712 := by
    simpa [prefixWord, tailWord_1668712, baseEnd_1668712] using wordTrace_append hprefix tailTrace_1668712
  have hstable : (prefixWord ++ tailWord_1668712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668712).length < 2 ^ (prefixWord ++ tailWord_1668712).sum := by decide
  have hdescent : baseEnd_1668712 < baseStart_1668712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668733 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1668733 : Nat := 118140960795 + 1668733 * 2 ^ 59
def prefixEnd_1668733 : Nat := 4983230072969 + 3 ^ 40 * 1668733 * 2
def baseEnd_1668733 : Nat := 285620704339774936054381

theorem tailTrace_1668733 : CollatzResearch.WordTrace tailWord_1668733 prefixEnd_1668733 285620704339774936054381 := by
  unfold tailWord_1668733
  simp only [CollatzResearch.WordTrace]
  refine ⟨60863692663472812751746853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40575795108981875167831235 60863692663472812751746853)
  ·
    refine ⟨11411942374401152390952535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60863692663472812751746853 11411942374401152390952535)
    ·
      refine ⟨17117913561601728586428803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11411942374401152390952535 17117913561601728586428803)
      ·
        refine ⟨25676870342402592879643205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17117913561601728586428803 25676870342402592879643205)
        ·
          refine ⟨4814413189200486164933101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25676870342402592879643205 4814413189200486164933101)
          ·
            refine ⟨1805404945950182311849913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4814413189200486164933101 1805404945950182311849913)
            ·
              refine ⟨1354053709462636733887435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1805404945950182311849913 1354053709462636733887435)
              ·
                refine ⟨2031080564193955100831153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354053709462636733887435 2031080564193955100831153)
                ·
                  refine ⟨1523310423145466325623365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2031080564193955100831153 1523310423145466325623365)
                  ·
                    refine ⟨285620704339774936054381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1523310423145466325623365 285620704339774936054381)
                    ·
                      rfl

theorem cell23_1668733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1668733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668733 prefixEnd_1668733 := by exact prefixLift 1668733
  have htrace : WordTrace (prefixWord ++ tailWord_1668733) baseStart_1668733 baseEnd_1668733 := by
    simpa [prefixWord, tailWord_1668733, baseEnd_1668733] using wordTrace_append hprefix tailTrace_1668733
  have hstable : (prefixWord ++ tailWord_1668733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668733).length < 2 ^ (prefixWord ++ tailWord_1668733).sum := by decide
  have hdescent : baseEnd_1668733 < baseStart_1668733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668790 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1668790 : Nat := 118140960795 + 1668790 * 2 ^ 59
def prefixEnd_1668790 : Nat := 4983230072969 + 3 ^ 40 * 1668790 * 2
def baseEnd_1668790 : Nat := 856891381416631085150381

theorem tailTrace_1668790 : CollatzResearch.WordTrace tailWord_1668790 prefixEnd_1668790 856891381416631085150381 := by
  unfold tailWord_1668790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804110726516644467910739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40577181082844207657714549 3804110726516644467910739)
  ·
    refine ⟨5706166089774966701866109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3804110726516644467910739 5706166089774966701866109)
    ·
      refine ⟨2139812283665612513199791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5706166089774966701866109 2139812283665612513199791)
      ·
        refine ⟨3209718425498418769799687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139812283665612513199791 3209718425498418769799687)
        ·
          refine ⟨4814577638247628154699531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209718425498418769799687 4814577638247628154699531)
          ·
            refine ⟨7221866457371442232049297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814577638247628154699531 7221866457371442232049297)
            ·
              refine ⟨5416399843028581674036973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7221866457371442232049297 5416399843028581674036973)
              ·
                refine ⟨2031149941135718127763865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5416399843028581674036973 2031149941135718127763865)
                ·
                  refine ⟨1523362455851788595822899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2031149941135718127763865 1523362455851788595822899)
                  ·
                    refine ⟨2285043683777682893734349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1523362455851788595822899 2285043683777682893734349)
                    ·
                      refine ⟨856891381416631085150381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2285043683777682893734349 856891381416631085150381)
                      ·
                        rfl

theorem cell23_1668790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1668790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668790 prefixEnd_1668790 := by exact prefixLift 1668790
  have htrace : WordTrace (prefixWord ++ tailWord_1668790) baseStart_1668790 baseEnd_1668790 := by
    simpa [prefixWord, tailWord_1668790, baseEnd_1668790] using wordTrace_append hprefix tailTrace_1668790
  have hstable : (prefixWord ++ tailWord_1668790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668790).length < 2 ^ (prefixWord ++ tailWord_1668790).sum := by decide
  have hdescent : baseEnd_1668790 < baseStart_1668790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668796 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_1668796 : Nat := 118140960795 + 1668796 * 2 ^ 59
def prefixEnd_1668796 : Nat := 4983230072969 + 3 ^ 40 * 1668796 * 2
def baseEnd_1668796 : Nat := 856894462300558061675353

theorem tailTrace_1668796 : CollatzResearch.WordTrace tailWord_1668796 prefixEnd_1668796 856894462300558061675353 := by
  unfold tailWord_1668796
  simp only [CollatzResearch.WordTrace]
  refine ⟨30432995231122287255645121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40577326974829716340860161 30432995231122287255645121)
  ·
    refine ⟨22824746423341715441733841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30432995231122287255645121 22824746423341715441733841)
    ·
      refine ⟨17118559817506286581300381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22824746423341715441733841 17118559817506286581300381)
      ·
        refine ⟨6419459931564857467987643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17118559817506286581300381 6419459931564857467987643)
        ·
          refine ⟨9629189897347286201981465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6419459931564857467987643 9629189897347286201981465)
          ·
            refine ⟨7221892423010464651486099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9629189897347286201981465 7221892423010464651486099)
            ·
              refine ⟨10832838634515696977229149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7221892423010464651486099 10832838634515696977229149)
              ·
                refine ⟨4062314487943386366460931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10832838634515696977229149 4062314487943386366460931)
                ·
                  refine ⟨6093471731915079549691397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062314487943386366460931 6093471731915079549691397)
                  ·
                    refine ⟨1142525949734077415567137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6093471731915079549691397 1142525949734077415567137)
                    ·
                      refine ⟨856894462300558061675353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1142525949734077415567137 856894462300558061675353)
                      ·
                        rfl

theorem cell23_1668796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_1668796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668796 prefixEnd_1668796 := by exact prefixLift 1668796
  have htrace : WordTrace (prefixWord ++ tailWord_1668796) baseStart_1668796 baseEnd_1668796 := by
    simpa [prefixWord, tailWord_1668796, baseEnd_1668796] using wordTrace_append hprefix tailTrace_1668796
  have hstable : (prefixWord ++ tailWord_1668796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668796).length < 2 ^ (prefixWord ++ tailWord_1668796).sum := by decide
  have hdescent : baseEnd_1668796 < baseStart_1668796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668866 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1668866 : Nat := 118140960795 + 1668866 * 2 ^ 59
def prefixEnd_1668866 : Nat := 4983230072969 + 3 ^ 40 * 1668866 * 2
def baseEnd_1668866 : Nat := 285643468648790929266677

theorem tailTrace_1668866 : CollatzResearch.WordTrace tailWord_1668866 prefixEnd_1668866 285643468648790929266677 := by
  unfold tailWord_1668866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15217135892997744116584613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40579029047993984310892301 15217135892997744116584613)
  ·
    refine ⟨2853212979937077021859615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15217135892997744116584613 2853212979937077021859615)
    ·
      refine ⟨4279819469905615532789423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2853212979937077021859615 4279819469905615532789423)
      ·
        refine ⟨6419729204858423299184135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279819469905615532789423 6419729204858423299184135)
        ·
          refine ⟨9629593807287634948776203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6419729204858423299184135 9629593807287634948776203)
          ·
            refine ⟨14444390710931452423164305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9629593807287634948776203 14444390710931452423164305)
            ·
              refine ⟨10833293033198589317373229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14444390710931452423164305 10833293033198589317373229)
              ·
                refine ⟨4062484887449470994014961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10833293033198589317373229 4062484887449470994014961)
                ·
                  refine ⟨3046863665587103245511221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4062484887449470994014961 3046863665587103245511221)
                  ·
                    refine ⟨285643468648790929266677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3046863665587103245511221 285643468648790929266677)
                    ·
                      rfl

theorem cell23_1668866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1668866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668866 prefixEnd_1668866 := by exact prefixLift 1668866
  have htrace : WordTrace (prefixWord ++ tailWord_1668866) baseStart_1668866 baseEnd_1668866 := by
    simpa [prefixWord, tailWord_1668866, baseEnd_1668866] using wordTrace_append hprefix tailTrace_1668866
  have hstable : (prefixWord ++ tailWord_1668866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668866).length < 2 ^ (prefixWord ++ tailWord_1668866).sum := by decide
  have hdescent : baseEnd_1668866 < baseStart_1668866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668976 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 4]
def baseStart_1668976 : Nat := 118140960795 + 1668976 * 2 ^ 59
def prefixEnd_1668976 : Nat := 4983230072969 + 3 ^ 40 * 1668976 * 2
def baseEnd_1668976 : Nat := 856986888818367357424525

theorem tailTrace_1668976 : CollatzResearch.WordTrace tailWord_1668976 prefixEnd_1668976 856986888818367357424525 := by
  unfold tailWord_1668976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30436277800796232626421391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40581703734394976835228521 30436277800796232626421391)
  ·
    refine ⟨45654416701194348939632087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30436277800796232626421391 45654416701194348939632087)
    ·
      refine ⟨68481625051791523409448131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45654416701194348939632087 68481625051791523409448131)
      ·
        refine ⟨102722437577687285114172197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68481625051791523409448131 102722437577687285114172197)
        ·
          refine ⟨19260457045816365958907287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102722437577687285114172197 19260457045816365958907287)
          ·
            refine ⟨28890685568724548938360931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19260457045816365958907287 28890685568724548938360931)
            ·
              refine ⟨43336028353086823407541397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28890685568724548938360931 43336028353086823407541397)
              ·
                refine ⟨2031376329050944847228503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43336028353086823407541397 2031376329050944847228503)
                ·
                  refine ⟨3047064493576417270842755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031376329050944847228503 3047064493576417270842755)
                  ·
                    refine ⟨4570596740364625906264133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3047064493576417270842755 4570596740364625906264133)
                    ·
                      refine ⟨856986888818367357424525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4570596740364625906264133 856986888818367357424525)
                      ·
                        rfl

theorem cell23_1668976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 4].length) (baseStart_1668976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668976 prefixEnd_1668976 := by exact prefixLift 1668976
  have htrace : WordTrace (prefixWord ++ tailWord_1668976) baseStart_1668976 baseEnd_1668976 := by
    simpa [prefixWord, tailWord_1668976, baseEnd_1668976] using wordTrace_append hprefix tailTrace_1668976
  have hstable : (prefixWord ++ tailWord_1668976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668976).length < 2 ^ (prefixWord ++ tailWord_1668976).sum := by decide
  have hdescent : baseEnd_1668976 < baseStart_1668976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668989 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_1668989 : Nat := 118140960795 + 1668989 * 2 ^ 59
def prefixEnd_1668989 : Nat := 4983230072969 + 3 ^ 40 * 1668989 * 2
def baseEnd_1668989 : Nat := 856993564066875806561965

theorem tailTrace_1668989 : CollatzResearch.WordTrace tailWord_1668989 prefixEnd_1668989 856993564066875806561965 := by
  unfold tailWord_1668989
  simp only [CollatzResearch.WordTrace]
  refine ⟨60873029750545368473066021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40582019833696912315377347 60873029750545368473066021)
  ·
    refine ⟨11413693078227256588699879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60873029750545368473066021 11413693078227256588699879)
    ·
      refine ⟨17120539617340884883049819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11413693078227256588699879 17120539617340884883049819)
      ·
        refine ⟨25680809426011327324574729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17120539617340884883049819 25680809426011327324574729)
        ·
          refine ⟨19260607069508495493431047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25680809426011327324574729 19260607069508495493431047)
          ·
            refine ⟨28890910604262743240146571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19260607069508495493431047 28890910604262743240146571)
            ·
              refine ⟨43336365906394114860219857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28890910604262743240146571 43336365906394114860219857)
              ·
                refine ⟨32502274429795586145164893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43336365906394114860219857 32502274429795586145164893)
                ·
                  refine ⟨12188352911173344804436835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32502274429795586145164893 12188352911173344804436835)
                  ·
                    refine ⟨18282529366760017206655253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12188352911173344804436835 18282529366760017206655253)
                    ·
                      refine ⟨856993564066875806561965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18282529366760017206655253 856993564066875806561965)
                      ·
                        rfl

theorem cell23_1668989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_1668989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668989 prefixEnd_1668989 := by exact prefixLift 1668989
  have htrace : WordTrace (prefixWord ++ tailWord_1668989) baseStart_1668989 baseEnd_1668989 := by
    simpa [prefixWord, tailWord_1668989, baseEnd_1668989] using wordTrace_append hprefix tailTrace_1668989
  have hstable : (prefixWord ++ tailWord_1668989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668989).length < 2 ^ (prefixWord ++ tailWord_1668989).sum := by decide
  have hdescent : baseEnd_1668989 < baseStart_1668989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1668990 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1668990 : Nat := 118140960795 + 1668990 * 2 ^ 59
def prefixEnd_1668990 : Nat := 4983230072969 + 3 ^ 40 * 1668990 * 2
def baseEnd_1668990 : Nat := 285664692515843434216487

theorem tailTrace_1668990 : CollatzResearch.WordTrace tailWord_1668990 prefixEnd_1668990 285664692515843434216487 := by
  unfold tailWord_1668990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609133277942718205481553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40582044149027830429234949 7609133277942718205481553)
  ·
    refine ⟨5706849958457038654111165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7609133277942718205481553 5706849958457038654111165)
    ·
      refine ⟨2140068734421389495291687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5706849958457038654111165 2140068734421389495291687)
      ·
        refine ⟨3210103101632084242937531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140068734421389495291687 3210103101632084242937531)
        ·
          refine ⟨4815154652448126364406297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210103101632084242937531 4815154652448126364406297)
          ·
            refine ⟨3611365989336094773304723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4815154652448126364406297 3611365989336094773304723)
            ·
              refine ⟨5417048984004142159957085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611365989336094773304723 5417048984004142159957085)
              ·
                refine ⟨2031393369001553309983907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5417048984004142159957085 2031393369001553309983907)
                ·
                  refine ⟨3047090053502329964975861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031393369001553309983907 3047090053502329964975861)
                  ·
                    refine ⟨285664692515843434216487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3047090053502329964975861 285664692515843434216487)
                    ·
                      rfl

theorem cell23_1668990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1668990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1668990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1668990 prefixEnd_1668990 := by exact prefixLift 1668990
  have htrace : WordTrace (prefixWord ++ tailWord_1668990) baseStart_1668990 baseEnd_1668990 := by
    simpa [prefixWord, tailWord_1668990, baseEnd_1668990] using wordTrace_append hprefix tailTrace_1668990
  have hstable : (prefixWord ++ tailWord_1668990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1668990).length < 2 ^ (prefixWord ++ tailWord_1668990).sum := by decide
  have hdescent : baseEnd_1668990 < baseStart_1668990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1668990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669029 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_1669029 : Nat := 118140960795 + 1669029 * 2 ^ 59
def prefixEnd_1669029 : Nat := 4983230072969 + 3 ^ 40 * 1669029 * 2
def baseEnd_1669029 : Nat := 285671367764351883353927

theorem tailTrace_1669029 : CollatzResearch.WordTrace tailWord_1669029 prefixEnd_1669029 285671367764351883353927 := by
  unfold tailWord_1669029
  simp only [CollatzResearch.WordTrace]
  refine ⟨60874488670400455304522141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40582992446933636869681427 60874488670400455304522141)
  ·
    refine ⟨22827933251400170739195803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60874488670400455304522141 22827933251400170739195803)
    ·
      refine ⟨34241899877100256108793705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22827933251400170739195803 34241899877100256108793705)
      ·
        refine ⟨25681424907825192081595279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34241899877100256108793705 25681424907825192081595279)
        ·
          refine ⟨38522137361737788122392919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25681424907825192081595279 38522137361737788122392919)
          ·
            refine ⟨57783206042606682183589379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38522137361737788122392919 57783206042606682183589379)
            ·
              refine ⟨86674809063910023275384069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57783206042606682183589379 86674809063910023275384069)
              ·
                refine ⟨16251526699483129364134513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86674809063910023275384069 16251526699483129364134513)
                ·
                  refine ⟨12188645024612347023100885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16251526699483129364134513 12188645024612347023100885)
                  ·
                    refine ⟨285671367764351883353927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12188645024612347023100885 285671367764351883353927)
                    ·
                      rfl

theorem cell23_1669029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_1669029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669029 prefixEnd_1669029 := by exact prefixLift 1669029
  have htrace : WordTrace (prefixWord ++ tailWord_1669029) baseStart_1669029 baseEnd_1669029 := by
    simpa [prefixWord, tailWord_1669029, baseEnd_1669029] using wordTrace_append hprefix tailTrace_1669029
  have hstable : (prefixWord ++ tailWord_1669029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669029).length < 2 ^ (prefixWord ++ tailWord_1669029).sum := by decide
  have hdescent : baseEnd_1669029 < baseStart_1669029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669038 : List Nat := [4, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1669038 : Nat := 118140960795 + 1669038 * 2 ^ 59
def prefixEnd_1669038 : Nat := 4983230072969 + 3 ^ 40 * 1669038 * 2
def baseEnd_1669038 : Nat := 857018724618946114849241

theorem tailTrace_1669038 : CollatzResearch.WordTrace tailWord_1669038 prefixEnd_1669038 857018724618946114849241 := by
  unfold tailWord_1669038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609352115920981230199971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40583211284911899894399845 7609352115920981230199971)
  ·
    refine ⟨11414028173881471845299957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7609352115920981230199971 11414028173881471845299957)
    ·
      refine ⟨1070065141301387985496871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11414028173881471845299957 1070065141301387985496871)
      ·
        refine ⟨1605097711952081978245307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070065141301387985496871 1605097711952081978245307)
        ·
          refine ⟨2407646567928122967367961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605097711952081978245307 2407646567928122967367961)
          ·
            refine ⟨1805734925946092225525971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2407646567928122967367961 1805734925946092225525971)
            ·
              refine ⟨2708602388919138338288957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805734925946092225525971 2708602388919138338288957)
              ·
                refine ⟨1015725895844676876858359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2708602388919138338288957 1015725895844676876858359)
                ·
                  refine ⟨1523588843767015315287539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015725895844676876858359 1523588843767015315287539)
                  ·
                    refine ⟨2285383265650522972931309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1523588843767015315287539 2285383265650522972931309)
                    ·
                      refine ⟨857018724618946114849241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2285383265650522972931309 857018724618946114849241)
                      ·
                        rfl

theorem cell23_1669038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1669038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669038 prefixEnd_1669038 := by exact prefixLift 1669038
  have htrace : WordTrace (prefixWord ++ tailWord_1669038) baseStart_1669038 baseEnd_1669038 := by
    simpa [prefixWord, tailWord_1669038, baseEnd_1669038] using wordTrace_append hprefix tailTrace_1669038
  have hstable : (prefixWord ++ tailWord_1669038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669038).length < 2 ^ (prefixWord ++ tailWord_1669038).sum := by decide
  have hdescent : baseEnd_1669038 < baseStart_1669038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669039 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_1669039 : Nat := 118140960795 + 1669039 * 2 ^ 59
def prefixEnd_1669039 : Nat := 4983230072969 + 3 ^ 40 * 1669039 * 2
def baseEnd_1669039 : Nat := 857019238099600610936735

theorem tailTrace_1669039 : CollatzResearch.WordTrace tailWord_1669039 prefixEnd_1669039 857019238099600610936735 := by
  unfold tailWord_1669039
  simp only [CollatzResearch.WordTrace]
  refine ⟨60874853400364227012386171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40583235600242818008257447 60874853400364227012386171)
  ·
    refine ⟨91312280100546340518579257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60874853400364227012386171 91312280100546340518579257)
    ·
      refine ⟨68484210075409755388934443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91312280100546340518579257 68484210075409755388934443)
      ·
        refine ⟨102726315113114633083401665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68484210075409755388934443 102726315113114633083401665)
        ·
          refine ⟨77044736334835974812551249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102726315113114633083401665 77044736334835974812551249)
          ·
            refine ⟨57783552251126981109413437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77044736334835974812551249 57783552251126981109413437)
            ·
              refine ⟨21668832094172617916030039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57783552251126981109413437 21668832094172617916030039)
              ·
                refine ⟨32503248141258926874045059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21668832094172617916030039 32503248141258926874045059)
                ·
                  refine ⟨48754872211888390311067589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32503248141258926874045059 48754872211888390311067589)
                  ·
                    refine ⟨9141538539729073183325173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48754872211888390311067589 9141538539729073183325173)
                    ·
                      refine ⟨857019238099600610936735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9141538539729073183325173 857019238099600610936735)
                      ·
                        rfl

theorem cell23_1669039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_1669039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669039 prefixEnd_1669039 := by exact prefixLift 1669039
  have htrace : WordTrace (prefixWord ++ tailWord_1669039) baseStart_1669039 baseEnd_1669039 := by
    simpa [prefixWord, tailWord_1669039, baseEnd_1669039] using wordTrace_append hprefix tailTrace_1669039
  have hstable : (prefixWord ++ tailWord_1669039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669039).length < 2 ^ (prefixWord ++ tailWord_1669039).sum := by decide
  have hdescent : baseEnd_1669039 < baseStart_1669039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669076 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1669076 : Nat := 118140960795 + 1669076 * 2 ^ 59
def prefixEnd_1669076 : Nat := 4983230072969 + 3 ^ 40 * 1669076 * 2
def baseEnd_1669076 : Nat := 285679412294605655391355

theorem tailTrace_1669076 : CollatzResearch.WordTrace tailWord_1669076 prefixEnd_1669076 285679412294605655391355 := by
  unfold tailWord_1669076
  simp only [CollatzResearch.WordTrace]
  refine ⟨30438101450615091165741541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40584135267486788220988721 30438101450615091165741541)
  ·
    refine ⟨5707144021990329593576539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30438101450615091165741541 5707144021990329593576539)
    ·
      refine ⟨8560716032985494390364809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5707144021990329593576539 8560716032985494390364809)
      ·
        refine ⟨6420537024739120792773607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8560716032985494390364809 6420537024739120792773607)
        ·
          refine ⟨9630805537108681189160411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6420537024739120792773607 9630805537108681189160411)
          ·
            refine ⟨14446208305663021783740617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9630805537108681189160411 14446208305663021783740617)
            ·
              refine ⟨10834656229247266337805463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14446208305663021783740617 10834656229247266337805463)
              ·
                refine ⟨16251984343870899506708195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10834656229247266337805463 16251984343870899506708195)
                ·
                  refine ⟨24377976515806349260062293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16251984343870899506708195 24377976515806349260062293)
                  ·
                    refine ⟨285679412294605655391355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24377976515806349260062293 285679412294605655391355)
                    ·
                      rfl

theorem cell23_1669076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1669076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669076 prefixEnd_1669076 := by exact prefixLift 1669076
  have htrace : WordTrace (prefixWord ++ tailWord_1669076) baseStart_1669076 baseEnd_1669076 := by
    simpa [prefixWord, tailWord_1669076, baseEnd_1669076] using wordTrace_append hprefix tailTrace_1669076
  have hstable : (prefixWord ++ tailWord_1669076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669076).length < 2 ^ (prefixWord ++ tailWord_1669076).sum := by decide
  have hdescent : baseEnd_1669076 < baseStart_1669076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669077 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_1669077 : Nat := 118140960795 + 1669077 * 2 ^ 59
def prefixEnd_1669077 : Nat := 4983230072969 + 3 ^ 40 * 1669077 * 2
def baseEnd_1669077 : Nat := 857038750364471462261561

theorem tailTrace_1669077 : CollatzResearch.WordTrace tailWord_1669077 prefixEnd_1669077 857038750364471462261561 := by
  unfold tailWord_1669077
  simp only [CollatzResearch.WordTrace]
  refine ⟨60876239374226559502269485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40584159582817706334846323 60876239374226559502269485)
  ·
    refine ⟨22828589765334959813351057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60876239374226559502269485 22828589765334959813351057)
    ·
      refine ⟨17121442324001219860013293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22828589765334959813351057 17121442324001219860013293)
      ·
        refine ⟨6420540871500457447504985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17121442324001219860013293 6420540871500457447504985)
        ·
          refine ⟨4815405653625343085628739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6420540871500457447504985 4815405653625343085628739)
          ·
            refine ⟨7223108480438014628443109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815405653625343085628739 7223108480438014628443109)
            ·
              refine ⟨1354332840082127742833083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7223108480438014628443109 1354332840082127742833083)
              ·
                refine ⟨2031499260123191614249625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354332840082127742833083 2031499260123191614249625)
                ·
                  refine ⟨1523624445092393710687219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2031499260123191614249625 1523624445092393710687219)
                  ·
                    refine ⟨2285436667638590566030829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1523624445092393710687219 2285436667638590566030829)
                    ·
                      refine ⟨857038750364471462261561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2285436667638590566030829 857038750364471462261561)
                      ·
                        rfl

theorem cell23_1669077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_1669077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669077 prefixEnd_1669077 := by exact prefixLift 1669077
  have htrace : WordTrace (prefixWord ++ tailWord_1669077) baseStart_1669077 baseEnd_1669077 := by
    simpa [prefixWord, tailWord_1669077, baseEnd_1669077] using wordTrace_append hprefix tailTrace_1669077
  have hstable : (prefixWord ++ tailWord_1669077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669077).length < 2 ^ (prefixWord ++ tailWord_1669077).sum := by decide
  have hdescent : baseEnd_1669077 < baseStart_1669077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669087 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 1, 3, 2]
def baseStart_1669087 : Nat := 118140960795 + 1669087 * 2 ^ 59
def prefixEnd_1669087 : Nat := 4983230072969 + 3 ^ 40 * 1669087 * 2
def baseEnd_1669087 : Nat := 857043885171016423136515

theorem tailTrace_1669087 : CollatzResearch.WordTrace tailWord_1669087 prefixEnd_1669087 857043885171016423136515 := by
  unfold tailWord_1669087
  simp only [CollatzResearch.WordTrace]
  refine ⟨60876604104190331210133515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40584402736126887473422343 60876604104190331210133515)
  ·
    refine ⟨91314906156285496815200273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60876604104190331210133515 91314906156285496815200273)
    ·
      refine ⟨68486179617214122611400205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91314906156285496815200273 68486179617214122611400205)
      ·
        refine ⟨25682317356455295979275077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68486179617214122611400205 25682317356455295979275077)
        ·
          refine ⟨4815434504335367996114077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25682317356455295979275077 4815434504335367996114077)
          ·
            refine ⟨1805787939125762998542779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4815434504335367996114077 1805787939125762998542779)
            ·
              refine ⟨2708681908688644497814169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805787939125762998542779 2708681908688644497814169)
              ·
                refine ⟨2031511431516483373360627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2708681908688644497814169 2031511431516483373360627)
                ·
                  refine ⟨3047267147274725060040941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031511431516483373360627 3047267147274725060040941)
                  ·
                    refine ⟨1142725180228021897515353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3047267147274725060040941 1142725180228021897515353)
                    ·
                      refine ⟨857043885171016423136515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1142725180228021897515353 857043885171016423136515)
                      ·
                        rfl

theorem cell23_1669087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_1669087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669087 prefixEnd_1669087 := by exact prefixLift 1669087
  have htrace : WordTrace (prefixWord ++ tailWord_1669087) baseStart_1669087 baseEnd_1669087 := by
    simpa [prefixWord, tailWord_1669087, baseEnd_1669087] using wordTrace_append hprefix tailTrace_1669087
  have hstable : (prefixWord ++ tailWord_1669087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669087).length < 2 ^ (prefixWord ++ tailWord_1669087).sum := by decide
  have hdescent : baseEnd_1669087 < baseStart_1669087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669096 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1669096 : Nat := 118140960795 + 1669096 * 2 ^ 59
def prefixEnd_1669096 : Nat := 4983230072969 + 3 ^ 40 * 1669096 * 2
def baseEnd_1669096 : Nat := 857048506496906887923973

theorem tailTrace_1669096 : CollatzResearch.WordTrace tailWord_1669096 prefixEnd_1669096 857048506496906887923973 := by
  unfold tailWord_1669096
  simp only [CollatzResearch.WordTrace]
  refine ⟨30438466180578862873605571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40584621574105150498140761 30438466180578862873605571)
  ·
    refine ⟨45657699270868294310408357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30438466180578862873605571 45657699270868294310408357)
    ·
      refine ⟨8560818613287805183201567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45657699270868294310408357 8560818613287805183201567)
      ·
        refine ⟨12841227919931707774802351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8560818613287805183201567 12841227919931707774802351)
        ·
          refine ⟨19261841879897561662203527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12841227919931707774802351 19261841879897561662203527)
          ·
            refine ⟨28892762819846342493305291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19261841879897561662203527 28892762819846342493305291)
            ·
              refine ⟨43339144229769513739957937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28892762819846342493305291 43339144229769513739957937)
              ·
                refine ⟨32504358172327135304968453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43339144229769513739957937 32504358172327135304968453)
                ·
                  refine ⟨6094567157311337869681585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32504358172327135304968453 6094567157311337869681585)
                  ·
                    refine ⟨4570925367983503402261189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6094567157311337869681585 4570925367983503402261189)
                    ·
                      refine ⟨857048506496906887923973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4570925367983503402261189 857048506496906887923973)
                      ·
                        rfl

theorem cell23_1669096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1669096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669096 prefixEnd_1669096 := by exact prefixLift 1669096
  have htrace : WordTrace (prefixWord ++ tailWord_1669096) baseStart_1669096 baseEnd_1669096 := by
    simpa [prefixWord, tailWord_1669096, baseEnd_1669096] using wordTrace_append hprefix tailTrace_1669096
  have hstable : (prefixWord ++ tailWord_1669096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669096).length < 2 ^ (prefixWord ++ tailWord_1669096).sum := by decide
  have hdescent : baseEnd_1669096 < baseStart_1669096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669153 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 1, 7]
def baseStart_1669153 : Nat := 118140960795 + 1669153 * 2 ^ 59
def prefixEnd_1669153 : Nat := 4983230072969 + 3 ^ 40 * 1669153 * 2
def baseEnd_1669153 : Nat := 285692591631404388303737

theorem tailTrace_1669153 : CollatzResearch.WordTrace tailWord_1669153 prefixEnd_1669153 285692591631404388303737 := by
  unfold tailWord_1669153
  simp only [CollatzResearch.WordTrace]
  refine ⟨60879011321951224482036113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40586007547967482988024075 60879011321951224482036113)
  ·
    refine ⟨45659258491463418361527085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60879011321951224482036113 45659258491463418361527085)
    ·
      refine ⟨17122221934298781885572657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45659258491463418361527085 17122221934298781885572657)
      ·
        refine ⟨12841666450724086414179493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17122221934298781885572657 12841666450724086414179493)
        ·
          refine ⟨2407812459510766202658655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12841666450724086414179493 2407812459510766202658655)
          ·
            refine ⟨3611718689266149303987983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407812459510766202658655 3611718689266149303987983)
            ·
              refine ⟨5417578033899223955981975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611718689266149303987983 5417578033899223955981975)
              ·
                refine ⟨8126367050848835933972963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417578033899223955981975 8126367050848835933972963)
                ·
                  refine ⟨12189550576273253900959445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8126367050848835933972963 12189550576273253900959445)
                  ·
                    refine ⟨285692591631404388303737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12189550576273253900959445 285692591631404388303737)
                    ·
                      rfl

theorem cell23_1669153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_1669153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669153 prefixEnd_1669153 := by exact prefixLift 1669153
  have htrace : WordTrace (prefixWord ++ tailWord_1669153) baseStart_1669153 baseEnd_1669153 := by
    simpa [prefixWord, tailWord_1669153, baseEnd_1669153] using wordTrace_append hprefix tailTrace_1669153
  have hstable : (prefixWord ++ tailWord_1669153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669153).length < 2 ^ (prefixWord ++ tailWord_1669153).sum := by decide
  have hdescent : baseEnd_1669153 < baseStart_1669153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669173 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1669173 : Nat := 118140960795 + 1669173 * 2 ^ 59
def prefixEnd_1669173 : Nat := 4983230072969 + 3 ^ 40 * 1669173 * 2
def baseEnd_1669173 : Nat := 857088044507303086661119

theorem tailTrace_1669173 : CollatzResearch.WordTrace tailWord_1669173 prefixEnd_1669173 857088044507303086661119 := by
  unfold tailWord_1669173
  simp only [CollatzResearch.WordTrace]
  refine ⟨60879740781878767897764173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40586493854585845265176115 60879740781878767897764173)
  ·
    refine ⟨22829902793204537961661565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60879740781878767897764173 22829902793204537961661565)
    ·
      refine ⟨8561213547451701735623087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22829902793204537961661565 8561213547451701735623087)
      ·
        refine ⟨12841820321177552603434631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8561213547451701735623087 12841820321177552603434631)
        ·
          refine ⟨19262730481766328905151947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12841820321177552603434631 19262730481766328905151947)
          ·
            refine ⟨28894095722649493357727921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19262730481766328905151947 28894095722649493357727921)
            ·
              refine ⟨21670571791987120018295941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28894095722649493357727921 21670571791987120018295941)
              ·
                refine ⟨4063232210997585003430489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21670571791987120018295941 4063232210997585003430489)
                ·
                  refine ⟨3047424158248188752572867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4063232210997585003430489 3047424158248188752572867)
                  ·
                    refine ⟨4571136237372283128859301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3047424158248188752572867 4571136237372283128859301)
                    ·
                      refine ⟨857088044507303086661119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4571136237372283128859301 857088044507303086661119)
                      ·
                        rfl

theorem cell23_1669173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1669173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669173 prefixEnd_1669173 := by exact prefixLift 1669173
  have htrace : WordTrace (prefixWord ++ tailWord_1669173) baseStart_1669173 baseEnd_1669173 := by
    simpa [prefixWord, tailWord_1669173, baseEnd_1669173] using wordTrace_append hprefix tailTrace_1669173
  have hstable : (prefixWord ++ tailWord_1669173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669173).length < 2 ^ (prefixWord ++ tailWord_1669173).sum := by decide
  have hdescent : baseEnd_1669173 < baseStart_1669173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669183 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 3, 4]
def baseStart_1669183 : Nat := 118140960795 + 1669183 * 2 ^ 59
def prefixEnd_1669183 : Nat := 4983230072969 + 3 ^ 40 * 1669183 * 2
def baseEnd_1669183 : Nat := 285697726437949349178691

theorem tailTrace_1669183 : CollatzResearch.WordTrace tailWord_1669183 prefixEnd_1669183 285697726437949349178691 := by
  unfold tailWord_1669183
  simp only [CollatzResearch.WordTrace]
  refine ⟨60880105511842539605628203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40586737007895026403752135 60880105511842539605628203)
  ·
    refine ⟨91320158267763809408442305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60880105511842539605628203 91320158267763809408442305)
    ·
      refine ⟨68490118700822857056331729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91320158267763809408442305 68490118700822857056331729)
      ·
        refine ⟨51367589025617142792248797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68490118700822857056331729 51367589025617142792248797)
        ·
          refine ⟨19262845884606428547093299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51367589025617142792248797 19262845884606428547093299)
          ·
            refine ⟨28894268826909642820639949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19262845884606428547093299 28894268826909642820639949)
            ·
              refine ⟨10835350810091116057739981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28894268826909642820639949 10835350810091116057739981)
              ·
                refine ⟨4063256553784168521652493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10835350810091116057739981 4063256553784168521652493)
                ·
                  refine ⟨1523721207669063195619685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4063256553784168521652493 1523721207669063195619685)
                  ·
                    refine ⟨285697726437949349178691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1523721207669063195619685 285697726437949349178691)
                    ·
                      rfl

theorem cell23_1669183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 4].length) (baseStart_1669183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669183 prefixEnd_1669183 := by exact prefixLift 1669183
  have htrace : WordTrace (prefixWord ++ tailWord_1669183) baseStart_1669183 baseEnd_1669183 := by
    simpa [prefixWord, tailWord_1669183, baseEnd_1669183] using wordTrace_append hprefix tailTrace_1669183
  have hstable : (prefixWord ++ tailWord_1669183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669183).length < 2 ^ (prefixWord ++ tailWord_1669183).sum := by decide
  have hdescent : baseEnd_1669183 < baseStart_1669183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669190 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1669190 : Nat := 118140960795 + 1669190 * 2 ^ 59
def prefixEnd_1669190 : Nat := 4983230072969 + 3 ^ 40 * 1669190 * 2
def baseEnd_1669190 : Nat := 857096773678429520148541

theorem tailTrace_1669190 : CollatzResearch.WordTrace tailWord_1669190 prefixEnd_1669190 857096773678429520148541 := by
  unfold tailWord_1669190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902511275713036868785407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40586907215211453200755349 1902511275713036868785407)
  ·
    refine ⟨2853766913569555303178111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1902511275713036868785407 2853766913569555303178111)
    ·
      refine ⟨4280650370354332954767167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2853766913569555303178111 4280650370354332954767167)
      ·
        refine ⟨6420975555531499432150751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4280650370354332954767167 6420975555531499432150751)
        ·
          refine ⟨9631463333297249148226127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6420975555531499432150751 9631463333297249148226127)
          ·
            refine ⟨14447194999945873722339191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631463333297249148226127 14447194999945873722339191)
            ·
              refine ⟨21670792499918810583508787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14447194999945873722339191 21670792499918810583508787)
              ·
                refine ⟨32506188749878215875263181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21670792499918810583508787 32506188749878215875263181)
                ·
                  refine ⟨12189820781204330953223693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32506188749878215875263181 12189820781204330953223693)
                  ·
                    refine ⟨4571182792951624107458885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12189820781204330953223693 4571182792951624107458885)
                    ·
                      refine ⟨857096773678429520148541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4571182792951624107458885 857096773678429520148541)
                      ·
                        rfl

theorem cell23_1669190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1669190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669190 prefixEnd_1669190 := by exact prefixLift 1669190
  have htrace : WordTrace (prefixWord ++ tailWord_1669190) baseStart_1669190 baseEnd_1669190 := by
    simpa [prefixWord, tailWord_1669190, baseEnd_1669190] using wordTrace_append hprefix tailTrace_1669190
  have hstable : (prefixWord ++ tailWord_1669190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669190).length < 2 ^ (prefixWord ++ tailWord_1669190).sum := by decide
  have hdescent : baseEnd_1669190 < baseStart_1669190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669234 : List Nat := [3, 2, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_1669234 : Nat := 118140960795 + 1669234 * 2 ^ 59
def prefixEnd_1669234 : Nat := 4983230072969 + 3 ^ 40 * 1669234 * 2
def baseEnd_1669234 : Nat := 285706455609075782666113

theorem tailTrace_1669234 : CollatzResearch.WordTrace tailWord_1669234 prefixEnd_1669234 285706455609075782666113 := by
  unfold tailWord_1669234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15220491408664443828933689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40587977089771850210489837 15220491408664443828933689)
  ·
    refine ⟨11415368556498332871700267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15220491408664443828933689 11415368556498332871700267)
    ·
      refine ⟨17123052834747499307550401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11415368556498332871700267 17123052834747499307550401)
      ·
        refine ⟨12842289626060624480662801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17123052834747499307550401 12842289626060624480662801)
        ·
          refine ⟨9631717219545468360497101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12842289626060624480662801 9631717219545468360497101)
          ·
            refine ⟨3611893957329550635186413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9631717219545468360497101 3611893957329550635186413)
            ·
              refine ⟨1354460233998581488194905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3611893957329550635186413 1354460233998581488194905)
              ·
                refine ⟨1015845175498936116146179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354460233998581488194905 1015845175498936116146179)
                ·
                  refine ⟨1523767763248404174219269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015845175498936116146179 1523767763248404174219269)
                  ·
                    refine ⟨285706455609075782666113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1523767763248404174219269 285706455609075782666113)
                    ·
                      rfl

theorem cell23_1669234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_1669234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669234 prefixEnd_1669234 := by exact prefixLift 1669234
  have htrace : WordTrace (prefixWord ++ tailWord_1669234) baseStart_1669234 baseEnd_1669234 := by
    simpa [prefixWord, tailWord_1669234, baseEnd_1669234] using wordTrace_append hprefix tailTrace_1669234
  have hstable : (prefixWord ++ tailWord_1669234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669234).length < 2 ^ (prefixWord ++ tailWord_1669234).sum := by decide
  have hdescent : baseEnd_1669234 < baseStart_1669234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669273 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 6, 4]
def baseStart_1669273 : Nat := 118140960795 + 1669273 * 2 ^ 59
def prefixEnd_1669273 : Nat := 4983230072969 + 3 ^ 40 * 1669273 * 2
def baseEnd_1669273 : Nat := 285713130857584231803553

theorem tailTrace_1669273 : CollatzResearch.WordTrace tailWord_1669273 prefixEnd_1669273 285713130857584231803553 := by
  unfold tailWord_1669273
  simp only [CollatzResearch.WordTrace]
  refine ⟨60883388081516484976404473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40588925387677656650936315 60883388081516484976404473)
  ·
    refine ⟨45662541061137363732303355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60883388081516484976404473 45662541061137363732303355)
    ·
      refine ⟨68493811591706045598455033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45662541061137363732303355 68493811591706045598455033)
      ·
        refine ⟨51370358693779534198841275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68493811591706045598455033 51370358693779534198841275)
        ·
          refine ⟨77055538040669301298261913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51370358693779534198841275 77055538040669301298261913)
          ·
            refine ⟨57791653530501975973696435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77055538040669301298261913 57791653530501975973696435)
            ·
              refine ⟨86687480295752963960544653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57791653530501975973696435 86687480295752963960544653)
              ·
                refine ⟨32507805110907361485204245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86687480295752963960544653 32507805110907361485204245)
                ·
                  refine ⟨1523803364573782569618949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32507805110907361485204245 1523803364573782569618949)
                  ·
                    refine ⟨285713130857584231803553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1523803364573782569618949 285713130857584231803553)
                    ·
                      rfl

theorem cell23_1669273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 4].length) (baseStart_1669273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669273 prefixEnd_1669273 := by exact prefixLift 1669273
  have htrace : WordTrace (prefixWord ++ tailWord_1669273) baseStart_1669273 baseEnd_1669273 := by
    simpa [prefixWord, tailWord_1669273, baseEnd_1669273] using wordTrace_append hprefix tailTrace_1669273
  have hstable : (prefixWord ++ tailWord_1669273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669273).length < 2 ^ (prefixWord ++ tailWord_1669273).sum := by decide
  have hdescent : baseEnd_1669273 < baseStart_1669273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669277 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1669277 : Nat := 118140960795 + 1669277 * 2 ^ 59
def prefixEnd_1669277 : Nat := 4983230072969 + 3 ^ 40 * 1669277 * 2
def baseEnd_1669277 : Nat := 285713815498456893253547

theorem tailTrace_1669277 : CollatzResearch.WordTrace tailWord_1669277 prefixEnd_1669277 285713815498456893253547 := by
  unfold tailWord_1669277
  simp only [CollatzResearch.WordTrace]
  refine ⟨60883533973501993659550085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40589022649001329106366723 60883533973501993659550085)
  ·
    refine ⟨11415662620031623811165641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60883533973501993659550085 11415662620031623811165641)
    ·
      refine ⟨8561746965023717858374231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11415662620031623811165641 8561746965023717858374231)
      ·
        refine ⟨12842620447535576787561347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8561746965023717858374231 12842620447535576787561347)
        ·
          refine ⟨19263930671303365181342021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12842620447535576787561347 19263930671303365181342021)
          ·
            refine ⟨3611987000869380971501629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19263930671303365181342021 3611987000869380971501629)
            ·
              refine ⟨1354495125326017864313111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3611987000869380971501629 1354495125326017864313111)
              ·
                refine ⟨2031742687989026796469667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354495125326017864313111 2031742687989026796469667)
                ·
                  refine ⟨3047614031983540194704501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031742687989026796469667 3047614031983540194704501)
                  ·
                    refine ⟨285713815498456893253547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3047614031983540194704501 285713815498456893253547)
                    ·
                      rfl

theorem cell23_1669277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1669277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669277 prefixEnd_1669277 := by exact prefixLift 1669277
  have htrace : WordTrace (prefixWord ++ tailWord_1669277) baseStart_1669277 baseEnd_1669277 := by
    simpa [prefixWord, tailWord_1669277, baseEnd_1669277] using wordTrace_append hprefix tailTrace_1669277
  have hstable : (prefixWord ++ tailWord_1669277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669277).length < 2 ^ (prefixWord ++ tailWord_1669277).sum := by decide
  have hdescent : baseEnd_1669277 < baseStart_1669277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669303 : List Nat := [1, 1, 3, 1, 4, 2, 3, 8]
def baseStart_1669303 : Nat := 118140960795 + 1669303 * 2 ^ 59
def prefixEnd_1669303 : Nat := 4983230072969 + 3 ^ 40 * 1669303 * 2
def baseEnd_1669303 : Nat := 31746473962681021408723

theorem tailTrace_1669303 : CollatzResearch.WordTrace tailWord_1669303 prefixEnd_1669303 31746473962681021408723 := by
  unfold tailWord_1669303
  simp only [CollatzResearch.WordTrace]
  refine ⟨60884482271407800099996563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40589654847605200066664375 60884482271407800099996563)
  ·
    refine ⟨91326723407111700149994845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60884482271407800099996563 91326723407111700149994845)
    ·
      refine ⟨34247521277666887556248067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91326723407111700149994845 34247521277666887556248067)
      ·
        refine ⟨51371281916500331334372101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34247521277666887556248067 51371281916500331334372101)
        ·
          refine ⟨9632115359343812125194769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51371281916500331334372101 9632115359343812125194769)
          ·
            refine ⟨7224086519507859093896077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9632115359343812125194769 7224086519507859093896077)
            ·
              refine ⟨2709032444815447160211029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7224086519507859093896077 2709032444815447160211029)
              ·
                refine ⟨31746473962681021408723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2709032444815447160211029 31746473962681021408723)
                ·
                  rfl

theorem cell23_1669303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 8].length) (baseStart_1669303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669303 prefixEnd_1669303 := by exact prefixLift 1669303
  have htrace : WordTrace (prefixWord ++ tailWord_1669303) baseStart_1669303 baseEnd_1669303 := by
    simpa [prefixWord, tailWord_1669303, baseEnd_1669303] using wordTrace_append hprefix tailTrace_1669303
  have hstable : (prefixWord ++ tailWord_1669303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669303).length < 2 ^ (prefixWord ++ tailWord_1669303).sum := by decide
  have hdescent : baseEnd_1669303 < baseStart_1669303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669314 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1669314 : Nat := 118140960795 + 1669314 * 2 ^ 59
def prefixEnd_1669314 : Nat := 4983230072969 + 3 ^ 40 * 1669314 * 2
def baseEnd_1669314 : Nat := 857160445279587034997971

theorem tailTrace_1669314 : CollatzResearch.WordTrace tailWord_1669314 prefixEnd_1669314 857160445279587034997971 := by
  unfold tailWord_1669314
  simp only [CollatzResearch.WordTrace]
  refine ⟨15221220868591987244661749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40589922316245299319097997 15221220868591987244661749)
  ·
    refine ⟨1426989456430498804187039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15221220868591987244661749 1426989456430498804187039)
    ·
      refine ⟨2140484184645748206280559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426989456430498804187039 2140484184645748206280559)
      ·
        refine ⟨3210726276968622309420839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140484184645748206280559 3210726276968622309420839)
        ·
          refine ⟨4816089415452933464131259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210726276968622309420839 4816089415452933464131259)
          ·
            refine ⟨7224134123179400196196889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816089415452933464131259 7224134123179400196196889)
            ·
              refine ⟨5418100592384550147147667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7224134123179400196196889 5418100592384550147147667)
              ·
                refine ⟨8127150888576825220721501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5418100592384550147147667 8127150888576825220721501)
                ·
                  refine ⟨3047681583216309457770563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8127150888576825220721501 3047681583216309457770563)
                  ·
                    refine ⟨4571522374824464186655845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3047681583216309457770563 4571522374824464186655845)
                    ·
                      refine ⟨857160445279587034997971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4571522374824464186655845 857160445279587034997971)
                      ·
                        rfl

theorem cell23_1669314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1669314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669314 prefixEnd_1669314 := by exact prefixLift 1669314
  have htrace : WordTrace (prefixWord ++ tailWord_1669314) baseStart_1669314 baseEnd_1669314 := by
    simpa [prefixWord, tailWord_1669314, baseEnd_1669314] using wordTrace_append hprefix tailTrace_1669314
  have hstable : (prefixWord ++ tailWord_1669314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669314).length < 2 ^ (prefixWord ++ tailWord_1669314).sum := by decide
  have hdescent : baseEnd_1669314 < baseStart_1669314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669363 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 2, 6]
def baseStart_1669363 : Nat := 118140960795 + 1669363 * 2 ^ 59
def prefixEnd_1669363 : Nat := 4983230072969 + 3 ^ 40 * 1669363 * 2
def baseEnd_1669363 : Nat := 285728535277219114428415

theorem tailTrace_1669363 : CollatzResearch.WordTrace tailWord_1669363 prefixEnd_1669363 285728535277219114428415 := by
  unfold tailWord_1669363
  simp only [CollatzResearch.WordTrace]
  refine ⟨60886670651190430347180743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40591113767460286898120495 60886670651190430347180743)
  ·
    refine ⟨91330005976785645520771115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60886670651190430347180743 91330005976785645520771115)
    ·
      refine ⟨136995008965178468281156673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91330005976785645520771115 136995008965178468281156673)
      ·
        refine ⟨102746256723883851210867505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136995008965178468281156673 102746256723883851210867505)
        ·
          refine ⟨77059692542912888408150629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102746256723883851210867505 77059692542912888408150629)
          ·
            refine ⟨14448692351796166576528243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77059692542912888408150629 14448692351796166576528243)
            ·
              refine ⟨21673038527694249864792365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14448692351796166576528243 21673038527694249864792365)
              ·
                refine ⟨8127389447885343699297137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21673038527694249864792365 8127389447885343699297137)
                ·
                  refine ⟨6095542085914007774472853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8127389447885343699297137 6095542085914007774472853)
                  ·
                    refine ⟨285728535277219114428415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6095542085914007774472853 285728535277219114428415)
                    ·
                      rfl

theorem cell23_1669363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 6].length) (baseStart_1669363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669363 prefixEnd_1669363 := by exact prefixLift 1669363
  have htrace : WordTrace (prefixWord ++ tailWord_1669363) baseStart_1669363 baseEnd_1669363 := by
    simpa [prefixWord, tailWord_1669363, baseEnd_1669363] using wordTrace_append hprefix tailTrace_1669363
  have hstable : (prefixWord ++ tailWord_1669363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669363).length < 2 ^ (prefixWord ++ tailWord_1669363).sum := by decide
  have hdescent : baseEnd_1669363 < baseStart_1669363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669373 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_1669373 : Nat := 118140960795 + 1669373 * 2 ^ 59
def prefixEnd_1669373 : Nat := 4983230072969 + 3 ^ 40 * 1669373 * 2
def baseEnd_1669373 : Nat := 857190740638202304160199

theorem tailTrace_1669373 : CollatzResearch.WordTrace tailWord_1669373 prefixEnd_1669373 857190740638202304160199 := by
  unfold tailWord_1669373
  simp only [CollatzResearch.WordTrace]
  refine ⟨60887035381154202055044773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40591356920769468036696515 60887035381154202055044773)
  ·
    refine ⟨11416319133966412885320895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60887035381154202055044773 11416319133966412885320895)
    ·
      refine ⟨17124478700949619327981343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11416319133966412885320895 17124478700949619327981343)
      ·
        refine ⟨25686718051424428991972015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17124478700949619327981343 25686718051424428991972015)
        ·
          refine ⟨38530077077136643487958023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25686718051424428991972015 38530077077136643487958023)
          ·
            refine ⟨57795115615704965231937035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38530077077136643487958023 57795115615704965231937035)
            ·
              refine ⟨86692673423557447847905553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57795115615704965231937035 86692673423557447847905553)
              ·
                refine ⟨65019505067668085885929165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86692673423557447847905553 65019505067668085885929165)
                ·
                  refine ⟨24382314400375532207223437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65019505067668085885929165 24382314400375532207223437)
                  ·
                    refine ⟨9143367900140824577708789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24382314400375532207223437 9143367900140824577708789)
                    ·
                      refine ⟨857190740638202304160199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9143367900140824577708789 857190740638202304160199)
                      ·
                        rfl

theorem cell23_1669373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_1669373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669373 prefixEnd_1669373 := by exact prefixLift 1669373
  have htrace : WordTrace (prefixWord ++ tailWord_1669373) baseStart_1669373 baseEnd_1669373 := by
    simpa [prefixWord, tailWord_1669373, baseEnd_1669373] using wordTrace_append hprefix tailTrace_1669373
  have hstable : (prefixWord ++ tailWord_1669373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669373).length < 2 ^ (prefixWord ++ tailWord_1669373).sum := by decide
  have hdescent : baseEnd_1669373 < baseStart_1669373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669387 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 6, 2, 2]
def baseStart_1669387 : Nat := 118140960795 + 1669387 * 2 ^ 59
def prefixEnd_1669387 : Nat := 4983230072969 + 3 ^ 40 * 1669387 * 2
def baseEnd_1669387 : Nat := 857197929367365249385135

theorem tailTrace_1669387 : CollatzResearch.WordTrace tailWord_1669387 prefixEnd_1669387 857197929367365249385135 := by
  unfold tailWord_1669387
  simp only [CollatzResearch.WordTrace]
  refine ⟨60887546003103482446054415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40591697335402321630702943 60887546003103482446054415)
  ·
    refine ⟨91331319004655223669081623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60887546003103482446054415 91331319004655223669081623)
    ·
      refine ⟨136996978506982835503622435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91331319004655223669081623 136996978506982835503622435)
      ·
        refine ⟨205495467760474253255433653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136996978506982835503622435 205495467760474253255433653)
        ·
          refine ⟨19265200102544461242696905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205495467760474253255433653 19265200102544461242696905)
          ·
            refine ⟨14448900076908345932022679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19265200102544461242696905 14448900076908345932022679)
            ·
              refine ⟨21673350115362518898034019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14448900076908345932022679 21673350115362518898034019)
              ·
                refine ⟨32510025173043778347051029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21673350115362518898034019 32510025173043778347051029)
                ·
                  refine ⟨1523907429986427110018017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32510025173043778347051029 1523907429986427110018017)
                  ·
                    refine ⟨1142930572489820332513513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1523907429986427110018017 1142930572489820332513513)
                    ·
                      refine ⟨857197929367365249385135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1142930572489820332513513 857197929367365249385135)
                      ·
                        rfl

theorem cell23_1669387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 2, 2].length) (baseStart_1669387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669387 prefixEnd_1669387 := by exact prefixLift 1669387
  have htrace : WordTrace (prefixWord ++ tailWord_1669387) baseStart_1669387 baseEnd_1669387 := by
    simpa [prefixWord, tailWord_1669387, baseEnd_1669387] using wordTrace_append hprefix tailTrace_1669387
  have hstable : (prefixWord ++ tailWord_1669387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669387).length < 2 ^ (prefixWord ++ tailWord_1669387).sum := by decide
  have hdescent : baseEnd_1669387 < baseStart_1669387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669390 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1669390 : Nat := 118140960795 + 1669390 * 2 ^ 59
def prefixEnd_1669390 : Nat := 4983230072969 + 3 ^ 40 * 1669390 * 2
def baseEnd_1669390 : Nat := 857199469809328737647621

theorem tailTrace_1669390 : CollatzResearch.WordTrace tailWord_1669390 prefixEnd_1669390 857199469809328737647621 := by
  unfold tailWord_1669390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7610956927761576744801703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40591770281395075972275749 7610956927761576744801703)
  ·
    refine ⟨11416435391642365117202555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7610956927761576744801703 11416435391642365117202555)
    ·
      refine ⟨17124653087463547675803833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11416435391642365117202555 17124653087463547675803833)
      ·
        refine ⟨12843489815597660756852875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17124653087463547675803833 12843489815597660756852875)
        ·
          refine ⟨19265234723396491135279313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12843489815597660756852875 19265234723396491135279313)
          ·
            refine ⟨14448926042547368351459485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19265234723396491135279313 14448926042547368351459485)
            ·
              refine ⟨5418347265955263131797307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14448926042547368351459485 5418347265955263131797307)
              ·
                refine ⟨8127520898932894697695961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5418347265955263131797307 8127520898932894697695961)
                ·
                  refine ⟨6095640674199671023271971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8127520898932894697695961 6095640674199671023271971)
                  ·
                    refine ⟨9143461011299506534907957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6095640674199671023271971 9143461011299506534907957)
                    ·
                      refine ⟨857199469809328737647621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9143461011299506534907957 857199469809328737647621)
                      ·
                        rfl

theorem cell23_1669390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1669390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669390 prefixEnd_1669390 := by exact prefixLift 1669390
  have htrace : WordTrace (prefixWord ++ tailWord_1669390) baseStart_1669390 baseEnd_1669390 := by
    simpa [prefixWord, tailWord_1669390, baseEnd_1669390] using wordTrace_append hprefix tailTrace_1669390
  have hstable : (prefixWord ++ tailWord_1669390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669390).length < 2 ^ (prefixWord ++ tailWord_1669390).sum := by decide
  have hdescent : baseEnd_1669390 < baseStart_1669390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669404 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_1669404 : Nat := 118140960795 + 1669404 * 2 ^ 59
def prefixEnd_1669404 : Nat := 4983230072969 + 3 ^ 40 * 1669404 * 2
def baseEnd_1669404 : Nat := 857206658538491682872557

theorem tailTrace_1669404 : CollatzResearch.WordTrace tailWord_1669404 prefixEnd_1669404 857206658538491682872557 := by
  unfold tailWord_1669404
  simp only [CollatzResearch.WordTrace]
  refine ⟨30444083022020947174711633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40592110696027929566282177 30444083022020947174711633)
  ·
    refine ⟨22833062266515710381033725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30444083022020947174711633 22833062266515710381033725)
    ·
      refine ⟨8562398349943391392887647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22833062266515710381033725 8562398349943391392887647)
      ·
        refine ⟨12843597524915087089331471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8562398349943391392887647 12843597524915087089331471)
        ·
          refine ⟨19265396287372630633997207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12843597524915087089331471 19265396287372630633997207)
          ·
            refine ⟨28898094431058945950995811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19265396287372630633997207 28898094431058945950995811)
            ·
              refine ⟨43347141646588418926493717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28898094431058945950995811 43347141646588418926493717)
              ·
                refine ⟨2031897264683832137179393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43347141646588418926493717 2031897264683832137179393)
                ·
                  refine ⟨1523922948512874102884545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2031897264683832137179393 1523922948512874102884545)
                  ·
                    refine ⟨1142942211384655577163409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1523922948512874102884545 1142942211384655577163409)
                    ·
                      refine ⟨857206658538491682872557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1142942211384655577163409 857206658538491682872557)
                      ·
                        rfl

theorem cell23_1669404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_1669404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669404 prefixEnd_1669404 := by exact prefixLift 1669404
  have htrace : WordTrace (prefixWord ++ tailWord_1669404) baseStart_1669404 baseEnd_1669404 := by
    simpa [prefixWord, tailWord_1669404, baseEnd_1669404] using wordTrace_append hprefix tailTrace_1669404
  have hstable : (prefixWord ++ tailWord_1669404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669404).length < 2 ^ (prefixWord ++ tailWord_1669404).sum := by decide
  have hdescent : baseEnd_1669404 < baseStart_1669404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669420 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_1669420 : Nat := 118140960795 + 1669420 * 2 ^ 59
def prefixEnd_1669420 : Nat := 4983230072969 + 3 ^ 40 * 1669420 * 2
def baseEnd_1669420 : Nat := 857214874228963620272483

theorem tailTrace_1669420 : CollatzResearch.WordTrace tailWord_1669420 prefixEnd_1669420 857214874228963620272483 := by
  unfold tailWord_1669420
  simp only [CollatzResearch.WordTrace]
  refine ⟨30444374805991964541002857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40592499741322619388003809 30444374805991964541002857)
  ·
    refine ⟨22833281104493973405752143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30444374805991964541002857 22833281104493973405752143)
    ·
      refine ⟨34249921656740960108628215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22833281104493973405752143 34249921656740960108628215)
      ·
        refine ⟨51374882485111440162942323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34249921656740960108628215 51374882485111440162942323)
        ·
          refine ⟨77062323727667160244413485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51374882485111440162942323 77062323727667160244413485)
          ·
            refine ⟨28898371397875185091655057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77062323727667160244413485 28898371397875185091655057)
            ·
              refine ⟨21673778548406388818741293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28898371397875185091655057 21673778548406388818741293)
              ·
                refine ⟨8127666955652395807027985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21673778548406388818741293 8127666955652395807027985)
                ·
                  refine ⟨6095750216739296855270989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8127666955652395807027985 6095750216739296855270989)
                  ·
                    refine ⟨2285906331277236320726621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6095750216739296855270989 2285906331277236320726621)
                    ·
                      refine ⟨857214874228963620272483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2285906331277236320726621 857214874228963620272483)
                      ·
                        rfl

theorem cell23_1669420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_1669420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669420 prefixEnd_1669420 := by exact prefixLift 1669420
  have htrace : WordTrace (prefixWord ++ tailWord_1669420) baseStart_1669420 baseEnd_1669420 := by
    simpa [prefixWord, tailWord_1669420, baseEnd_1669420] using wordTrace_append hprefix tailTrace_1669420
  have hstable : (prefixWord ++ tailWord_1669420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669420).length < 2 ^ (prefixWord ++ tailWord_1669420).sum := by decide
  have hdescent : baseEnd_1669420 < baseStart_1669420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669423 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 3, 7]
def baseStart_1669423 : Nat := 118140960795 + 1669423 * 2 ^ 59
def prefixEnd_1669423 : Nat := 4983230072969 + 3 ^ 40 * 1669423 * 2
def baseEnd_1669423 : Nat := 285738804890309036178323

theorem tailTrace_1669423 : CollatzResearch.WordTrace tailWord_1669423 prefixEnd_1669423 285738804890309036178323 := by
  unfold tailWord_1669423
  simp only [CollatzResearch.WordTrace]
  refine ⟨60888859030973060594364923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40592572687315373729576615 60888859030973060594364923)
  ·
    refine ⟨91333288546459590891547385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60888859030973060594364923 91333288546459590891547385)
    ·
      refine ⟨68499966409844693168660539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91333288546459590891547385 68499966409844693168660539)
      ·
        refine ⟨102749949614767039752990809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68499966409844693168660539 102749949614767039752990809)
        ·
          refine ⟨77062462211075279814743107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102749949614767039752990809 77062462211075279814743107)
          ·
            refine ⟨115593693316612919722114661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77062462211075279814743107 115593693316612919722114661)
            ·
              refine ⟨21673817496864922447896499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115593693316612919722114661 21673817496864922447896499)
              ·
                refine ⟨32510726245297383671844749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21673817496864922447896499 32510726245297383671844749)
                ·
                  refine ⟨12191522341986518876941781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32510726245297383671844749 12191522341986518876941781)
                  ·
                    refine ⟨285738804890309036178323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12191522341986518876941781 285738804890309036178323)
                    ·
                      rfl

theorem cell23_1669423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_1669423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669423 prefixEnd_1669423 := by exact prefixLift 1669423
  have htrace : WordTrace (prefixWord ++ tailWord_1669423) baseStart_1669423 baseEnd_1669423 := by
    simpa [prefixWord, tailWord_1669423, baseEnd_1669423] using wordTrace_append hprefix tailTrace_1669423
  have hstable : (prefixWord ++ tailWord_1669423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669423).length < 2 ^ (prefixWord ++ tailWord_1669423).sum := by decide
  have hdescent : baseEnd_1669423 < baseStart_1669423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669461 : List Nat := [1, 3, 2, 2, 4, 2, 2, 2, 5]
def baseStart_1669461 : Nat := 118140960795 + 1669461 * 2 ^ 59
def prefixEnd_1669461 : Nat := 4983230072969 + 3 ^ 40 * 1669461 * 2
def baseEnd_1669461 : Nat := 95248436326199773317755

theorem tailTrace_1669461 : CollatzResearch.WordTrace tailWord_1669461 prefixEnd_1669461 95248436326199773317755 := by
  unfold tailWord_1669461
  simp only [CollatzResearch.WordTrace]
  refine ⟨60890245004835393084248237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40593496669890262056165491 60890245004835393084248237)
  ·
    refine ⟨22833841876813272406593089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60890245004835393084248237 22833841876813272406593089)
    ·
      refine ⟨17125381407609954304944817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22833841876813272406593089 17125381407609954304944817)
      ·
        refine ⟨12844036055707465728708613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17125381407609954304944817 12844036055707465728708613)
        ·
          refine ⟨2408256760445149824132865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12844036055707465728708613 2408256760445149824132865)
          ·
            refine ⟨1806192570333862368099649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2408256760445149824132865 1806192570333862368099649)
            ·
              refine ⟨1354644427750396776074737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1806192570333862368099649 1354644427750396776074737)
              ·
                refine ⟨1015983320812797582056053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354644427750396776074737 1015983320812797582056053)
                ·
                  refine ⟨95248436326199773317755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1015983320812797582056053 95248436326199773317755)
                  ·
                    rfl

theorem cell23_1669461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_1669461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669461 prefixEnd_1669461 := by exact prefixLift 1669461
  have htrace : WordTrace (prefixWord ++ tailWord_1669461) baseStart_1669461 baseEnd_1669461 := by
    simpa [prefixWord, tailWord_1669461, baseEnd_1669461] using wordTrace_append hprefix tailTrace_1669461
  have hstable : (prefixWord ++ tailWord_1669461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669461).length < 2 ^ (prefixWord ++ tailWord_1669461).sum := by decide
  have hdescent : baseEnd_1669461 < baseStart_1669461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669477 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 1, 6, 2]
def baseStart_1669477 : Nat := 118140960795 + 1669477 * 2 ^ 59
def prefixEnd_1669477 : Nat := 4983230072969 + 3 ^ 40 * 1669477 * 2
def baseEnd_1669477 : Nat := 857244142626269897259721

theorem tailTrace_1669477 : CollatzResearch.WordTrace tailWord_1669477 prefixEnd_1669477 857244142626269897259721 := by
  unfold tailWord_1669477
  simp only [CollatzResearch.WordTrace]
  refine ⟨60890828572777427816830685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40593885715184951877887123 60890828572777427816830685)
  ·
    refine ⟨22834060714791535431311507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60890828572777427816830685 22834060714791535431311507)
    ·
      refine ⟨34251091072187303146967261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22834060714791535431311507 34251091072187303146967261)
      ·
        refine ⟨12844159152070238680112723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34251091072187303146967261 12844159152070238680112723)
        ·
          refine ⟨19266238728105358020169085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12844159152070238680112723 19266238728105358020169085)
          ·
            refine ⟨7224839523039509257563407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19266238728105358020169085 7224839523039509257563407)
            ·
              refine ⟨10837259284559263886345111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7224839523039509257563407 10837259284559263886345111)
              ·
                refine ⟨16255888926838895829517667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10837259284559263886345111 16255888926838895829517667)
                ·
                  refine ⟨24383833390258343744276501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16255888926838895829517667 24383833390258343744276501)
                  ·
                    refine ⟨1142992190168359863012961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24383833390258343744276501 1142992190168359863012961)
                    ·
                      refine ⟨857244142626269897259721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1142992190168359863012961 857244142626269897259721)
                      ·
                        rfl

theorem cell23_1669477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_1669477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669477 prefixEnd_1669477 := by exact prefixLift 1669477
  have htrace : WordTrace (prefixWord ++ tailWord_1669477) baseStart_1669477 baseEnd_1669477 := by
    simpa [prefixWord, tailWord_1669477, baseEnd_1669477] using wordTrace_append hprefix tailTrace_1669477
  have hstable : (prefixWord ++ tailWord_1669477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669477).length < 2 ^ (prefixWord ++ tailWord_1669477).sum := by decide
  have hdescent : baseEnd_1669477 < baseStart_1669477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669540 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1669540 : Nat := 118140960795 + 1669540 * 2 ^ 59
def prefixEnd_1669540 : Nat := 4983230072969 + 3 ^ 40 * 1669540 * 2
def baseEnd_1669540 : Nat := 857276491907503150771931

theorem tailTrace_1669540 : CollatzResearch.WordTrace tailWord_1669540 prefixEnd_1669540 857276491907503150771931 := by
  unfold tailWord_1669540
  simp only [CollatzResearch.WordTrace]
  refine ⟨30446563185774594788187037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40595417581032793050916049 30446563185774594788187037)
  ·
    refine ⟨11417461194665473045570139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30446563185774594788187037 11417461194665473045570139)
    ·
      refine ⟨17126191791998209568355209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11417461194665473045570139 17126191791998209568355209)
      ·
        refine ⟨12844643843998657176266407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17126191791998209568355209 12844643843998657176266407)
        ·
          refine ⟨19266965765997985764399611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12844643843998657176266407 19266965765997985764399611)
          ·
            refine ⟨28900448648996978646599417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19266965765997985764399611 28900448648996978646599417)
            ·
              refine ⟨21675336486747733984949563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28900448648996978646599417 21675336486747733984949563)
              ·
                refine ⟨32513004730121600977424345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21675336486747733984949563 32513004730121600977424345)
                ·
                  refine ⟨24384753547591200733068259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32513004730121600977424345 24384753547591200733068259)
                  ·
                    refine ⟨36577130321386801099602389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24384753547591200733068259 36577130321386801099602389)
                    ·
                      refine ⟨857276491907503150771931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36577130321386801099602389 857276491907503150771931)
                      ·
                        rfl

theorem cell23_1669540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1669540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669540 prefixEnd_1669540 := by exact prefixLift 1669540
  have htrace : WordTrace (prefixWord ++ tailWord_1669540) baseStart_1669540 baseEnd_1669540 := by
    simpa [prefixWord, tailWord_1669540, baseEnd_1669540] using wordTrace_append hprefix tailTrace_1669540
  have hstable : (prefixWord ++ tailWord_1669540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669540).length < 2 ^ (prefixWord ++ tailWord_1669540).sum := by decide
  have hdescent : baseEnd_1669540 < baseStart_1669540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669554 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_1669554 : Nat := 118140960795 + 1669554 * 2 ^ 59
def prefixEnd_1669554 : Nat := 4983230072969 + 3 ^ 40 * 1669554 * 2
def baseEnd_1669554 : Nat := 857283680636666095996867

theorem tailTrace_1669554 : CollatzResearch.WordTrace tailWord_1669554 prefixEnd_1669554 857283680636666095996867 := by
  unfold tailWord_1669554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223409248374617491845929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40595757995665646644922477 15223409248374617491845929)
  ·
    refine ⟨11417556936280963118884447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15223409248374617491845929 11417556936280963118884447)
    ·
      refine ⟨17126335404421444678326671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11417556936280963118884447 17126335404421444678326671)
      ·
        refine ⟨25689503106632167017490007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17126335404421444678326671 25689503106632167017490007)
        ·
          refine ⟨38534254659948250526235011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25689503106632167017490007 38534254659948250526235011)
          ·
            refine ⟨57801381989922375789352517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38534254659948250526235011 57801381989922375789352517)
            ·
              refine ⟨10837759123110445460503597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57801381989922375789352517 10837759123110445460503597)
              ·
                refine ⟨4064159671166417047688849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10837759123110445460503597 4064159671166417047688849)
                ·
                  refine ⟨3048119753374812785766637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4064159671166417047688849 3048119753374812785766637)
                  ·
                    refine ⟨1143044907515554794662489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048119753374812785766637 1143044907515554794662489)
                    ·
                      refine ⟨857283680636666095996867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143044907515554794662489 857283680636666095996867)
                      ·
                        rfl

theorem cell23_1669554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_1669554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669554 prefixEnd_1669554 := by exact prefixLift 1669554
  have htrace : WordTrace (prefixWord ++ tailWord_1669554) baseStart_1669554 baseEnd_1669554 := by
    simpa [prefixWord, tailWord_1669554, baseEnd_1669554] using wordTrace_append hprefix tailTrace_1669554
  have hstable : (prefixWord ++ tailWord_1669554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669554).length < 2 ^ (prefixWord ++ tailWord_1669554).sum := by decide
  have hdescent : baseEnd_1669554 < baseStart_1669554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669560 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 3, 6]
def baseStart_1669560 : Nat := 118140960795 + 1669560 * 2 ^ 59
def prefixEnd_1669560 : Nat := 4983230072969 + 3 ^ 40 * 1669560 * 2
def baseEnd_1669560 : Nat := 285762253840197690840613

theorem tailTrace_1669560 : CollatzResearch.WordTrace tailWord_1669560 prefixEnd_1669560 285762253840197690840613 := by
  unfold tailWord_1669560
  simp only [CollatzResearch.WordTrace]
  refine ⟨30446927915738366496051067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40595903887651155328068089 30446927915738366496051067)
  ·
    refine ⟨45670391873607549744076601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30446927915738366496051067 45670391873607549744076601)
    ·
      refine ⟨34252793905205662308057451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45670391873607549744076601 34252793905205662308057451)
      ·
        refine ⟨51379190857808493462086177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34252793905205662308057451 51379190857808493462086177)
        ·
          refine ⟨38534393143356370096564633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51379190857808493462086177 38534393143356370096564633)
          ·
            refine ⟨28900794857517277572423475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38534393143356370096564633 28900794857517277572423475)
            ·
              refine ⟨43351192286275916358635213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28900794857517277572423475 43351192286275916358635213)
              ·
                refine ⟨16256697107353468634488205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43351192286275916358635213 16256697107353468634488205)
                ·
                  refine ⟨6096261415257550737933077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16256697107353468634488205 6096261415257550737933077)
                  ·
                    refine ⟨285762253840197690840613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6096261415257550737933077 285762253840197690840613)
                    ·
                      rfl

theorem cell23_1669560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_1669560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669560 prefixEnd_1669560 := by exact prefixLift 1669560
  have htrace : WordTrace (prefixWord ++ tailWord_1669560) baseStart_1669560 baseEnd_1669560 := by
    simpa [prefixWord, tailWord_1669560, baseEnd_1669560] using wordTrace_append hprefix tailTrace_1669560
  have hstable : (prefixWord ++ tailWord_1669560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669560).length < 2 ^ (prefixWord ++ tailWord_1669560).sum := by decide
  have hdescent : baseEnd_1669560 < baseStart_1669560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669564 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_1669564 : Nat := 118140960795 + 1669564 * 2 ^ 59
def prefixEnd_1669564 : Nat := 4983230072969 + 3 ^ 40 * 1669564 * 2
def baseEnd_1669564 : Nat := 285762938481070352290607

theorem tailTrace_1669564 : CollatzResearch.WordTrace tailWord_1669564 prefixEnd_1669564 285762938481070352290607 := by
  unfold tailWord_1669564
  simp only [CollatzResearch.WordTrace]
  refine ⟨30447000861731120837623873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40596001148974827783498497 30447000861731120837623873)
  ·
    refine ⟨22835250646298340628217905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30447000861731120837623873 22835250646298340628217905)
    ·
      refine ⟨17126437984723755471163429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22835250646298340628217905 17126437984723755471163429)
      ·
        refine ⟨3211207122135704150843143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17126437984723755471163429 3211207122135704150843143)
        ·
          refine ⟨4816810683203556226264715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211207122135704150843143 4816810683203556226264715)
          ·
            refine ⟨7225216024805334339397073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816810683203556226264715 7225216024805334339397073)
            ·
              refine ⟨5418912018604000754547805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7225216024805334339397073 5418912018604000754547805)
              ·
                refine ⟨2032092006976500282955427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5418912018604000754547805 2032092006976500282955427)
                ·
                  refine ⟨3048138010464750424433141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032092006976500282955427 3048138010464750424433141)
                  ·
                    refine ⟨285762938481070352290607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3048138010464750424433141 285762938481070352290607)
                    ·
                      rfl

theorem cell23_1669564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_1669564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669564 prefixEnd_1669564 := by exact prefixLift 1669564
  have htrace : WordTrace (prefixWord ++ tailWord_1669564) baseStart_1669564 baseEnd_1669564 := by
    simpa [prefixWord, tailWord_1669564, baseEnd_1669564] using wordTrace_append hprefix tailTrace_1669564
  have hstable : (prefixWord ++ tailWord_1669564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669564).length < 2 ^ (prefixWord ++ tailWord_1669564).sum := by decide
  have hdescent : baseEnd_1669564 < baseStart_1669564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669577 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 4, 4]
def baseStart_1669577 : Nat := 118140960795 + 1669577 * 2 ^ 59
def prefixEnd_1669577 : Nat := 4983230072969 + 3 ^ 40 * 1669577 * 2
def baseEnd_1669577 : Nat := 285765163563906502003087

theorem tailTrace_1669577 : CollatzResearch.WordTrace tailWord_1669577 prefixEnd_1669577 285765163563906502003087 := by
  unfold tailWord_1669577
  simp only [CollatzResearch.WordTrace]
  refine ⟨60894475872415144895470985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40596317248276763263647323 60894475872415144895470985)
  ·
    refine ⟨45670856904311358671603239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60894475872415144895470985 45670856904311358671603239)
    ·
      refine ⟨68506285356467038007404859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45670856904311358671603239 68506285356467038007404859)
      ·
        refine ⟨102759428034700557011107289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68506285356467038007404859 102759428034700557011107289)
        ·
          refine ⟨77069571026025417758330467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102759428034700557011107289 77069571026025417758330467)
          ·
            refine ⟨115604356539038126637495701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77069571026025417758330467 115604356539038126637495701)
            ·
              refine ⟨5418954212767412186132611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115604356539038126637495701 5418954212767412186132611)
              ·
                refine ⟨8128431319151118279198917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5418954212767412186132611 8128431319151118279198917)
                ·
                  refine ⟨1524080872340834677349797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8128431319151118279198917 1524080872340834677349797)
                  ·
                    refine ⟨285765163563906502003087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524080872340834677349797 285765163563906502003087)
                    ·
                      rfl

theorem cell23_1669577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 4].length) (baseStart_1669577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669577 prefixEnd_1669577 := by exact prefixLift 1669577
  have htrace : WordTrace (prefixWord ++ tailWord_1669577) baseStart_1669577 baseEnd_1669577 := by
    simpa [prefixWord, tailWord_1669577, baseEnd_1669577] using wordTrace_append hprefix tailTrace_1669577
  have hstable : (prefixWord ++ tailWord_1669577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669577).length < 2 ^ (prefixWord ++ tailWord_1669577).sum := by decide
  have hdescent : baseEnd_1669577 < baseStart_1669577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669578 : List Nat := [3, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3]
def baseStart_1669578 : Nat := 118140960795 + 1669578 * 2 ^ 59
def prefixEnd_1669578 : Nat := 4983230072969 + 3 ^ 40 * 1669578 * 2
def baseEnd_1669578 : Nat := 857296004172374002096757

theorem tailTrace_1669578 : CollatzResearch.WordTrace tailWord_1669578 prefixEnd_1669578 857296004172374002096757 := by
  unfold tailWord_1669578
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223628086352880516564347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40596341563607681377504925 15223628086352880516564347)
  ·
    refine ⟨22835442129529320774846521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15223628086352880516564347 22835442129529320774846521)
    ·
      refine ⟨17126581597146990581134891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22835442129529320774846521 17126581597146990581134891)
      ·
        refine ⟨25689872395720485871702337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17126581597146990581134891 25689872395720485871702337)
        ·
          refine ⟨19267404296790364403776753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25689872395720485871702337 19267404296790364403776753)
          ·
            refine ⟨14450553222592773302832565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19267404296790364403776753 14450553222592773302832565)
            ·
              refine ⟨1354739364618072497140553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14450553222592773302832565 1354739364618072497140553)
              ·
                refine ⟨1016054523463554372855415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354739364618072497140553 1016054523463554372855415)
                ·
                  refine ⟨1524081785195331559283123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016054523463554372855415 1524081785195331559283123)
                  ·
                    refine ⟨2286122677792997338924685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1524081785195331559283123 2286122677792997338924685)
                    ·
                      refine ⟨857296004172374002096757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2286122677792997338924685 857296004172374002096757)
                      ·
                        rfl

theorem cell23_1669578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_1669578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669578 prefixEnd_1669578 := by exact prefixLift 1669578
  have htrace : WordTrace (prefixWord ++ tailWord_1669578) baseStart_1669578 baseEnd_1669578 := by
    simpa [prefixWord, tailWord_1669578, baseEnd_1669578] using wordTrace_append hprefix tailTrace_1669578
  have hstable : (prefixWord ++ tailWord_1669578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669578).length < 2 ^ (prefixWord ++ tailWord_1669578).sum := by decide
  have hdescent : baseEnd_1669578 < baseStart_1669578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669594 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_1669594 : Nat := 118140960795 + 1669594 * 2 ^ 59
def prefixEnd_1669594 : Nat := 4983230072969 + 3 ^ 40 * 1669594 * 2
def baseEnd_1669594 : Nat := 285768073287615313165561

theorem tailTrace_1669594 : CollatzResearch.WordTrace tailWord_1669594 prefixEnd_1669594 285768073287615313165561 := by
  unfold tailWord_1669594
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223773978338389199709959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40596730608902371199226557 15223773978338389199709959)
  ·
    refine ⟨22835660967507583799564939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15223773978338389199709959 22835660967507583799564939)
    ·
      refine ⟨34253491451261375699347409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22835660967507583799564939 34253491451261375699347409)
      ·
        refine ⟨25690118588446031774510557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34253491451261375699347409 25690118588446031774510557)
        ·
          refine ⟨9633794470667261915441459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25690118588446031774510557 9633794470667261915441459)
          ·
            refine ⟨14450691706000892873162189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9633794470667261915441459 14450691706000892873162189)
            ·
              refine ⟨5419009389750334827435821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14450691706000892873162189 5419009389750334827435821)
              ·
                refine ⟨2032128521156375560288433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5419009389750334827435821 2032128521156375560288433)
                ·
                  refine ⟨1524096390867281670216325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032128521156375560288433 1524096390867281670216325)
                  ·
                    refine ⟨285768073287615313165561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524096390867281670216325 285768073287615313165561)
                    ·
                      rfl

theorem cell23_1669594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_1669594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669594 prefixEnd_1669594 := by exact prefixLift 1669594
  have htrace : WordTrace (prefixWord ++ tailWord_1669594) baseStart_1669594 baseEnd_1669594 := by
    simpa [prefixWord, tailWord_1669594, baseEnd_1669594] using wordTrace_append hprefix tailTrace_1669594
  have hstable : (prefixWord ++ tailWord_1669594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669594).length < 2 ^ (prefixWord ++ tailWord_1669594).sum := by decide
  have hdescent : baseEnd_1669594 < baseStart_1669594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669597 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1669597 : Nat := 118140960795 + 1669597 * 2 ^ 59
def prefixEnd_1669597 : Nat := 4983230072969 + 3 ^ 40 * 1669597 * 2
def baseEnd_1669597 : Nat := 857305760304809427759169

theorem tailTrace_1669597 : CollatzResearch.WordTrace tailWord_1669597 prefixEnd_1669597 857305760304809427759169 := by
  unfold tailWord_1669597
  simp only [CollatzResearch.WordTrace]
  refine ⟨60895205332342688311199045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40596803554895125540799363 60895205332342688311199045)
  ·
    refine ⟨11417850999814254058349821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60895205332342688311199045 11417850999814254058349821)
    ·
      refine ⟨4281694124930345271881183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11417850999814254058349821 4281694124930345271881183)
      ·
        refine ⟨6422541187395517907821775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281694124930345271881183 6422541187395517907821775)
        ·
          refine ⟨9633811781093276861732663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422541187395517907821775 9633811781093276861732663)
          ·
            refine ⟨14450717671639915292598995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9633811781093276861732663 14450717671639915292598995)
            ·
              refine ⟨21676076507459872938898493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14450717671639915292598995 21676076507459872938898493)
              ·
                refine ⟨8128528690297452352086935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21676076507459872938898493 8128528690297452352086935)
                ·
                  refine ⟨12192793035446178528130403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128528690297452352086935 12192793035446178528130403)
                  ·
                    refine ⟨18289189553169267792195605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12192793035446178528130403 18289189553169267792195605)
                    ·
                      refine ⟨857305760304809427759169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18289189553169267792195605 857305760304809427759169)
                      ·
                        rfl

theorem cell23_1669597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1669597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669597 prefixEnd_1669597 := by exact prefixLift 1669597
  have htrace : WordTrace (prefixWord ++ tailWord_1669597) baseStart_1669597 baseEnd_1669597 := by
    simpa [prefixWord, tailWord_1669597, baseEnd_1669597] using wordTrace_append hprefix tailTrace_1669597
  have hstable : (prefixWord ++ tailWord_1669597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669597).length < 2 ^ (prefixWord ++ tailWord_1669597).sum := by decide
  have hdescent : baseEnd_1669597 < baseStart_1669597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669614 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_1669614 : Nat := 118140960795 + 1669614 * 2 ^ 59
def prefixEnd_1669614 : Nat := 4983230072969 + 3 ^ 40 * 1669614 * 2
def baseEnd_1669614 : Nat := 857314489475935861246591

theorem tailTrace_1669614 : CollatzResearch.WordTrace tailWord_1669614 prefixEnd_1669614 857314489475935861246591 := by
  unfold tailWord_1669614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7611978171660137526820987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40597216915520733476378597 7611978171660137526820987)
  ·
    refine ⟨11417967257490206290231481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7611978171660137526820987 11417967257490206290231481)
    ·
      refine ⟨8563475443117654717673611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11417967257490206290231481 8563475443117654717673611)
      ·
        refine ⟨12845213164676482076510417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8563475443117654717673611 12845213164676482076510417)
        ·
          refine ⟨9633909873507361557382813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12845213164676482076510417 9633909873507361557382813)
          ·
            refine ⟨3612716202565260584018555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9633909873507361557382813 3612716202565260584018555)
            ·
              refine ⟨5419074303847890876027833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612716202565260584018555 5419074303847890876027833)
              ·
                refine ⟨4064305727885918157020875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419074303847890876027833 4064305727885918157020875)
                ·
                  refine ⟨6096458591828877235531313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064305727885918157020875 6096458591828877235531313)
                  ·
                    refine ⟨4572343943871657926648485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6096458591828877235531313 4572343943871657926648485)
                    ·
                      refine ⟨857314489475935861246591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4572343943871657926648485 857314489475935861246591)
                      ·
                        rfl

theorem cell23_1669614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_1669614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669614 prefixEnd_1669614 := by exact prefixLift 1669614
  have htrace : WordTrace (prefixWord ++ tailWord_1669614) baseStart_1669614 baseEnd_1669614 := by
    simpa [prefixWord, tailWord_1669614, baseEnd_1669614] using wordTrace_append hprefix tailTrace_1669614
  have hstable : (prefixWord ++ tailWord_1669614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669614).length < 2 ^ (prefixWord ++ tailWord_1669614).sum := by decide
  have hdescent : baseEnd_1669614 < baseStart_1669614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669618 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_1669618 : Nat := 118140960795 + 1669618 * 2 ^ 59
def prefixEnd_1669618 : Nat := 4983230072969 + 3 ^ 40 * 1669618 * 2
def baseEnd_1669618 : Nat := 857316543398553845596573

theorem tailTrace_1669618 : CollatzResearch.WordTrace tailWord_1669618 prefixEnd_1669618 857316543398553845596573 := by
  unfold tailWord_1669618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223992816316652224428377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40597314176844405931809005 15223992816316652224428377)
  ·
    refine ⟨11417994612237489168321283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15223992816316652224428377 11417994612237489168321283)
    ·
      refine ⟨17126991918356233752481925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11417994612237489168321283 17126991918356233752481925)
      ·
        refine ⟨3211310984691793828590361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17126991918356233752481925 3211310984691793828590361)
        ·
          refine ⟨2408483238518845371442771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3211310984691793828590361 2408483238518845371442771)
          ·
            refine ⟨3612724857778268057164157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408483238518845371442771 3612724857778268057164157)
            ·
              refine ⟨1354771821666850521436559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3612724857778268057164157 1354771821666850521436559)
              ·
                refine ⟨2032157732500275782154839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354771821666850521436559 2032157732500275782154839)
                ·
                  refine ⟨3048236598750413673232259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032157732500275782154839 3048236598750413673232259)
                  ·
                    refine ⟨4572354898125620509848389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3048236598750413673232259 4572354898125620509848389)
                    ·
                      refine ⟨857316543398553845596573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4572354898125620509848389 857316543398553845596573)
                      ·
                        rfl

theorem cell23_1669618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_1669618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669618 prefixEnd_1669618 := by exact prefixLift 1669618
  have htrace : WordTrace (prefixWord ++ tailWord_1669618) baseStart_1669618 baseEnd_1669618 := by
    simpa [prefixWord, tailWord_1669618, baseEnd_1669618] using wordTrace_append hprefix tailTrace_1669618
  have hstable : (prefixWord ++ tailWord_1669618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669618).length < 2 ^ (prefixWord ++ tailWord_1669618).sum := by decide
  have hdescent : baseEnd_1669618 < baseStart_1669618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669661 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_1669661 : Nat := 118140960795 + 1669661 * 2 ^ 59
def prefixEnd_1669661 : Nat := 4983230072969 + 3 ^ 40 * 1669661 * 2
def baseEnd_1669661 : Nat := 857338623066697177358875

theorem tailTrace_1669661 : CollatzResearch.WordTrace tailWord_1669661 prefixEnd_1669661 857338623066697177358875 := by
  unfold tailWord_1669661
  simp only [CollatzResearch.WordTrace]
  refine ⟨60897539604110827241528837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40598359736073884827685891 60897539604110827241528837)
  ·
    refine ⟨11418288675770780107786657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60897539604110827241528837 11418288675770780107786657)
    ·
      refine ⟨8563716506828085080839993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11418288675770780107786657 8563716506828085080839993)
      ·
        refine ⟨6422787380121063810629995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8563716506828085080839993 6422787380121063810629995)
        ·
          refine ⟨9634181070181595715944993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422787380121063810629995 9634181070181595715944993)
          ·
            refine ⟨7225635802636196786958745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9634181070181595715944993 7225635802636196786958745)
            ·
              refine ⟨5419226851977147590219059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7225635802636196786958745 5419226851977147590219059)
              ·
                refine ⟨8128840277965721385328589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419226851977147590219059 8128840277965721385328589)
                ·
                  refine ⟨3048315104237145519498221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8128840277965721385328589 3048315104237145519498221)
                  ·
                    refine ⟨1143118164088929569811833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3048315104237145519498221 1143118164088929569811833)
                    ·
                      refine ⟨857338623066697177358875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143118164088929569811833 857338623066697177358875)
                      ·
                        rfl

theorem cell23_1669661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_1669661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669661 prefixEnd_1669661 := by exact prefixLift 1669661
  have htrace : WordTrace (prefixWord ++ tailWord_1669661) baseStart_1669661 baseEnd_1669661 := by
    simpa [prefixWord, tailWord_1669661, baseEnd_1669661] using wordTrace_append hprefix tailTrace_1669661
  have hstable : (prefixWord ++ tailWord_1669661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669661).length < 2 ^ (prefixWord ++ tailWord_1669661).sum := by decide
  have hdescent : baseEnd_1669661 < baseStart_1669661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669687 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_1669687 : Nat := 118140960795 + 1669687 * 2 ^ 59
def prefixEnd_1669687 : Nat := 4983230072969 + 3 ^ 40 * 1669687 * 2
def baseEnd_1669687 : Nat := 857351973563714075633755

theorem tailTrace_1669687 : CollatzResearch.WordTrace tailWord_1669687 prefixEnd_1669687 857351973563714075633755 := by
  unfold tailWord_1669687
  simp only [CollatzResearch.WordTrace]
  refine ⟨60898487902016633681975315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40598991934677755787983543 60898487902016633681975315)
  ·
    refine ⟨91347731853024950522962973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60898487902016633681975315 91347731853024950522962973)
    ·
      refine ⟨34255399444884356446111115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91347731853024950522962973 34255399444884356446111115)
      ·
        refine ⟨51383099167326534669166673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34255399444884356446111115 51383099167326534669166673)
        ·
          refine ⟨38537324375494901001875005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51383099167326534669166673 38537324375494901001875005)
          ·
            refine ⟨14451496640810587875703127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38537324375494901001875005 14451496640810587875703127)
            ·
              refine ⟨21677244961215881813554691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14451496640810587875703127 21677244961215881813554691)
              ·
                refine ⟨32515867441823822720332037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21677244961215881813554691 32515867441823822720332037)
                ·
                  refine ⟨6096725145341966760062257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32515867441823822720332037 6096725145341966760062257)
                  ·
                    refine ⟨4572543859006475070046693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6096725145341966760062257 4572543859006475070046693)
                    ·
                      refine ⟨857351973563714075633755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4572543859006475070046693 857351973563714075633755)
                      ·
                        rfl

theorem cell23_1669687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_1669687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669687 prefixEnd_1669687 := by exact prefixLift 1669687
  have htrace : WordTrace (prefixWord ++ tailWord_1669687) baseStart_1669687 baseEnd_1669687 := by
    simpa [prefixWord, tailWord_1669687, baseEnd_1669687] using wordTrace_append hprefix tailTrace_1669687
  have hstable : (prefixWord ++ tailWord_1669687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669687).length < 2 ^ (prefixWord ++ tailWord_1669687).sum := by decide
  have hdescent : baseEnd_1669687 < baseStart_1669687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669702 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_1669702 : Nat := 118140960795 + 1669702 * 2 ^ 59
def prefixEnd_1669702 : Nat := 4983230072969 + 3 ^ 40 * 1669702 * 2
def baseEnd_1669702 : Nat := 857359675773531516946187

theorem tailTrace_1669702 : CollatzResearch.WordTrace tailWord_1669702 prefixEnd_1669702 857359675773531516946187 := by
  unfold tailWord_1669702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903094843655071601367855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40599356664641527495847573 1903094843655071601367855)
  ·
    refine ⟨2854642265482607402051783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1903094843655071601367855 2854642265482607402051783)
    ·
      refine ⟨4281963398223911103077675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2854642265482607402051783 4281963398223911103077675)
      ·
        refine ⟨6422945097335866654616513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281963398223911103077675 6422945097335866654616513)
        ·
          refine ⟨4817208823001899990962385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6422945097335866654616513 4817208823001899990962385)
          ·
            refine ⟨3612906617251424993221789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4817208823001899990962385 3612906617251424993221789)
            ·
              refine ⟨1354839981469284372458171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3612906617251424993221789 1354839981469284372458171)
              ·
                refine ⟨2032259972203926558687257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354839981469284372458171 2032259972203926558687257)
                ·
                  refine ⟨1524194979152944919015443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032259972203926558687257 1524194979152944919015443)
                  ·
                    refine ⟨2286292468729417378523165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1524194979152944919015443 2286292468729417378523165)
                    ·
                      refine ⟨857359675773531516946187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2286292468729417378523165 857359675773531516946187)
                      ·
                        rfl

theorem cell23_1669702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_1669702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669702 prefixEnd_1669702 := by exact prefixLift 1669702
  have htrace : WordTrace (prefixWord ++ tailWord_1669702) baseStart_1669702 baseEnd_1669702 := by
    simpa [prefixWord, tailWord_1669702, baseEnd_1669702] using wordTrace_append hprefix tailTrace_1669702
  have hstable : (prefixWord ++ tailWord_1669702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669702).length < 2 ^ (prefixWord ++ tailWord_1669702).sum := by decide
  have hdescent : baseEnd_1669702 < baseStart_1669702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669727 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 6, 5]
def baseStart_1669727 : Nat := 118140960795 + 1669727 * 2 ^ 59
def prefixEnd_1669727 : Nat := 4983230072969 + 3 ^ 40 * 1669727 * 2
def baseEnd_1669727 : Nat := 285790837596631306377857

theorem tailTrace_1669727 : CollatzResearch.WordTrace tailWord_1669727 prefixEnd_1669727 285790837596631306377857 := by
  unfold tailWord_1669727
  simp only [CollatzResearch.WordTrace]
  refine ⟨60899946821871720513431435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40599964547914480342287623 60899946821871720513431435)
  ·
    refine ⟨91349920232807580770147153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60899946821871720513431435 91349920232807580770147153)
    ·
      refine ⟨68512440174605685577610365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91349920232807580770147153 68512440174605685577610365)
      ·
        refine ⟨25692165065477132091603887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68512440174605685577610365 25692165065477132091603887)
        ·
          refine ⟨38538247598215698137405831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25692165065477132091603887 38538247598215698137405831)
          ·
            refine ⟨57807371397323547206108747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38538247598215698137405831 57807371397323547206108747)
            ·
              refine ⟨86711057095985320809163121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57807371397323547206108747 86711057095985320809163121)
              ·
                refine ⟨65033292821988990606872341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86711057095985320809163121 65033292821988990606872341)
                ·
                  refine ⟨3048435601030733934697141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65033292821988990606872341 3048435601030733934697141)
                  ·
                    refine ⟨285790837596631306377857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3048435601030733934697141 285790837596631306377857)
                    ·
                      rfl

theorem cell23_1669727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_1669727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669727 prefixEnd_1669727 := by exact prefixLift 1669727
  have htrace : WordTrace (prefixWord ++ tailWord_1669727) baseStart_1669727 baseEnd_1669727 := by
    simpa [prefixWord, tailWord_1669727, baseEnd_1669727] using wordTrace_append hprefix tailTrace_1669727
  have hstable : (prefixWord ++ tailWord_1669727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669727).length < 2 ^ (prefixWord ++ tailWord_1669727).sum := by decide
  have hdescent : baseEnd_1669727 < baseStart_1669727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669737 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_1669737 : Nat := 118140960795 + 1669737 * 2 ^ 59
def prefixEnd_1669737 : Nat := 4983230072969 + 3 ^ 40 * 1669737 * 2
def baseEnd_1669737 : Nat := 857377647596438880008525

theorem tailTrace_1669737 : CollatzResearch.WordTrace tailWord_1669737 prefixEnd_1669737 857377647596438880008525 := by
  unfold tailWord_1669737
  simp only [CollatzResearch.WordTrace]
  refine ⟨60900311551835492221295465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40600207701223661480863643 60900311551835492221295465)
  ·
    refine ⟨45675233663876619165971599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60900311551835492221295465 45675233663876619165971599)
    ·
      refine ⟨68512850495814928748957399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45675233663876619165971599 68512850495814928748957399)
      ·
        refine ⟨102769275743722393123436099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68512850495814928748957399 102769275743722393123436099)
        ·
          refine ⟨154153913615583589685154149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102769275743722393123436099 154153913615583589685154149)
          ·
            refine ⟨28903858802921923065966403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154153913615583589685154149 28903858802921923065966403)
            ·
              refine ⟨43355788204382884598949605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28903858802921923065966403 43355788204382884598949605)
              ·
                refine ⟨8129210288321790862303051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43355788204382884598949605 8129210288321790862303051)
                ·
                  refine ⟨12193815432482686293454577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129210288321790862303051 12193815432482686293454577)
                  ·
                    refine ⟨9145361574362014720090933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12193815432482686293454577 9145361574362014720090933)
                    ·
                      refine ⟨857377647596438880008525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9145361574362014720090933 857377647596438880008525)
                      ·
                        rfl

theorem cell23_1669737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_1669737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669737 prefixEnd_1669737 := by exact prefixLift 1669737
  have htrace : WordTrace (prefixWord ++ tailWord_1669737) baseStart_1669737 baseEnd_1669737 := by
    simpa [prefixWord, tailWord_1669737, baseEnd_1669737] using wordTrace_append hprefix tailTrace_1669737
  have hstable : (prefixWord ++ tailWord_1669737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669737).length < 2 ^ (prefixWord ++ tailWord_1669737).sum := by decide
  have hdescent : baseEnd_1669737 < baseStart_1669737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669747 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 4]
def baseStart_1669747 : Nat := 118140960795 + 1669747 * 2 ^ 59
def prefixEnd_1669747 : Nat := 4983230072969 + 3 ^ 40 * 1669747 * 2
def baseEnd_1669747 : Nat := 857382782402983840883479

theorem tailTrace_1669747 : CollatzResearch.WordTrace tailWord_1669747 prefixEnd_1669747 857382782402983840883479 := by
  unfold tailWord_1669747
  simp only [CollatzResearch.WordTrace]
  refine ⟨60900676281799263929159495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40600450854532842619439663 60900676281799263929159495)
  ·
    refine ⟨91351014422698895893739243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60900676281799263929159495 91351014422698895893739243)
    ·
      refine ⟨137026521634048343840608865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91351014422698895893739243 137026521634048343840608865)
      ·
        refine ⟨102769891225536257880456649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137026521634048343840608865 102769891225536257880456649)
        ·
          refine ⟨77077418419152193410342487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102769891225536257880456649 77077418419152193410342487)
          ·
            refine ⟨115616127628728290115513731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77077418419152193410342487 115616127628728290115513731)
            ·
              refine ⟨173424191443092435173270597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115616127628728290115513731 173424191443092435173270597)
              ·
                refine ⟨32517035895579831594988237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173424191443092435173270597 32517035895579831594988237)
                ·
                  refine ⟨12193888460842436848120589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32517035895579831594988237 12193888460842436848120589)
                  ·
                    refine ⟨4572708172815913818045221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12193888460842436848120589 4572708172815913818045221)
                    ·
                      refine ⟨857382782402983840883479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4572708172815913818045221 857382782402983840883479)
                      ·
                        rfl

theorem cell23_1669747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_1669747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669747 prefixEnd_1669747 := by exact prefixLift 1669747
  have htrace : WordTrace (prefixWord ++ tailWord_1669747) baseStart_1669747 baseEnd_1669747 := by
    simpa [prefixWord, tailWord_1669747, baseEnd_1669747] using wordTrace_append hprefix tailTrace_1669747
  have hstable : (prefixWord ++ tailWord_1669747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669747).length < 2 ^ (prefixWord ++ tailWord_1669747).sum := by decide
  have hdescent : baseEnd_1669747 < baseStart_1669747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669825 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1669825 : Nat := 118140960795 + 1669825 * 2 ^ 59
def prefixEnd_1669825 : Nat := 4983230072969 + 3 ^ 40 * 1669825 * 2
def baseEnd_1669825 : Nat := 285807611298011511902707

theorem tailTrace_1669825 : CollatzResearch.WordTrace tailWord_1669825 prefixEnd_1669825 285807611298011511902707 := by
  unfold tailWord_1669825
  simp only [CollatzResearch.WordTrace]
  refine ⟨60903521175516683250498929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40602347450344455500332619 60903521175516683250498929)
  ·
    refine ⟨45677640881637512437874197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60903521175516683250498929 45677640881637512437874197)
    ·
      refine ⟨2141139416326758395525353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45677640881637512437874197 2141139416326758395525353)
      ·
        refine ⟨1605854562245068796644015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2141139416326758395525353 1605854562245068796644015)
        ·
          refine ⟨2408781843367603194966023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605854562245068796644015 2408781843367603194966023)
          ·
            refine ⟨3613172765051404792449035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408781843367603194966023 3613172765051404792449035)
            ·
              refine ⟨5419759147577107188673553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613172765051404792449035 5419759147577107188673553)
              ·
                refine ⟨4064819360682830391505165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419759147577107188673553 4064819360682830391505165)
                ·
                  refine ⟨1524307260256061396814437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4064819360682830391505165 1524307260256061396814437)
                  ·
                    refine ⟨285807611298011511902707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524307260256061396814437 285807611298011511902707)
                    ·
                      rfl

theorem cell23_1669825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1669825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669825 prefixEnd_1669825 := by exact prefixLift 1669825
  have htrace : WordTrace (prefixWord ++ tailWord_1669825) baseStart_1669825 baseEnd_1669825 := by
    simpa [prefixWord, tailWord_1669825, baseEnd_1669825] using wordTrace_append hprefix tailTrace_1669825
  have hstable : (prefixWord ++ tailWord_1669825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669825).length < 2 ^ (prefixWord ++ tailWord_1669825).sum := by decide
  have hdescent : baseEnd_1669825 < baseStart_1669825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669841 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 1, 5, 2]
def baseStart_1669841 : Nat := 118140960795 + 1669841 * 2 ^ 59
def prefixEnd_1669841 : Nat := 4983230072969 + 3 ^ 40 * 1669841 * 2
def baseEnd_1669841 : Nat := 857431049584506473108047

theorem tailTrace_1669841 : CollatzResearch.WordTrace tailWord_1669841 prefixEnd_1669841 857431049584506473108047 := by
  unfold tailWord_1669841
  simp only [CollatzResearch.WordTrace]
  refine ⟨60904104743458717983081377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40602736495639145322054251 60904104743458717983081377)
  ·
    refine ⟨45678078557594038487311033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60904104743458717983081377 45678078557594038487311033)
    ·
      refine ⟨34258558918195528865483275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45678078557594038487311033 34258558918195528865483275)
      ·
        refine ⟨51387838377293293298224913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34258558918195528865483275 51387838377293293298224913)
        ·
          refine ⟨38540878782969969973668685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51387838377293293298224913 38540878782969969973668685)
          ·
            refine ⟨14452829543613738740125757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38540878782969969973668685 14452829543613738740125757)
            ·
              refine ⟨5419811078855152027547159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14452829543613738740125757 5419811078855152027547159)
              ·
                refine ⟨8129716618282728041320739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419811078855152027547159 8129716618282728041320739)
                ·
                  refine ⟨12194574927424092061981109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129716618282728041320739 12194574927424092061981109)
                  ·
                    refine ⟨1143241399446008630810729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12194574927424092061981109 1143241399446008630810729)
                    ·
                      refine ⟨857431049584506473108047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143241399446008630810729 857431049584506473108047)
                      ·
                        rfl

theorem cell23_1669841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_1669841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669841 prefixEnd_1669841 := by exact prefixLift 1669841
  have htrace : WordTrace (prefixWord ++ tailWord_1669841) baseStart_1669841 baseEnd_1669841 := by
    simpa [prefixWord, tailWord_1669841, baseEnd_1669841] using wordTrace_append hprefix tailTrace_1669841
  have hstable : (prefixWord ++ tailWord_1669841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669841).length < 2 ^ (prefixWord ++ tailWord_1669841).sum := by decide
  have hdescent : baseEnd_1669841 < baseStart_1669841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669881 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 2, 4]
def baseStart_1669881 : Nat := 118140960795 + 1669881 * 2 ^ 59
def prefixEnd_1669881 : Nat := 4983230072969 + 3 ^ 40 * 1669881 * 2
def baseEnd_1669881 : Nat := 285817196270228772202621

theorem tailTrace_1669881 : CollatzResearch.WordTrace tailWord_1669881 prefixEnd_1669881 285817196270228772202621 := by
  unfold tailWord_1669881
  simp only [CollatzResearch.WordTrace]
  refine ⟨60905563663313804814537497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40603709108875869876358331 60905563663313804814537497)
  ·
    refine ⟨45679172747485353610903123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60905563663313804814537497 45679172747485353610903123)
    ·
      refine ⟨68518759121228030416354685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45679172747485353610903123 68518759121228030416354685)
      ·
        refine ⟨25694534670460511406133007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68518759121228030416354685 25694534670460511406133007)
        ·
          refine ⟨38541802005690767109199511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25694534670460511406133007 38541802005690767109199511)
          ·
            refine ⟨57812703008536150663799267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38541802005690767109199511 57812703008536150663799267)
            ·
              refine ⟨86719054512804225995698901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57812703008536150663799267 86719054512804225995698901)
              ·
                refine ⟨2032477840143849046774193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86719054512804225995698901 2032477840143849046774193)
                ·
                  refine ⟨1524358380107886785080645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032477840143849046774193 1524358380107886785080645)
                  ·
                    refine ⟨285817196270228772202621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524358380107886785080645 285817196270228772202621)
                    ·
                      rfl

theorem cell23_1669881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 4].length) (baseStart_1669881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669881 prefixEnd_1669881 := by exact prefixLift 1669881
  have htrace : WordTrace (prefixWord ++ tailWord_1669881) baseStart_1669881 baseEnd_1669881 := by
    simpa [prefixWord, tailWord_1669881, baseEnd_1669881] using wordTrace_append hprefix tailTrace_1669881
  have hstable : (prefixWord ++ tailWord_1669881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669881).length < 2 ^ (prefixWord ++ tailWord_1669881).sum := by decide
  have hdescent : baseEnd_1669881 < baseStart_1669881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669911 : List Nat := [1, 1, 3, 4, 3, 2, 9]
def baseStart_1669911 : Nat := 118140960795 + 1669911 * 2 ^ 59
def prefixEnd_1669911 : Nat := 4983230072969 + 3 ^ 40 * 1669911 * 2
def baseEnd_1669911 : Nat := 10586012262102730854725

theorem tailTrace_1669911 : CollatzResearch.WordTrace tailWord_1669911 prefixEnd_1669911 10586012262102730854725 := by
  unfold tailWord_1669911
  simp only [CollatzResearch.WordTrace]
  refine ⟨60906657853205119938129587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40604438568803413292086391 60906657853205119938129587)
  ·
    refine ⟨91359986779807679907194381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60906657853205119938129587 91359986779807679907194381)
    ·
      refine ⟨34259995042427879965197893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91359986779807679907194381 34259995042427879965197893)
      ·
        refine ⟨6423749070455227493474605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34259995042427879965197893 6423749070455227493474605)
        ·
          refine ⟨2408905901420710310052977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6423749070455227493474605 2408905901420710310052977)
          ·
            refine ⟨1806679426065532732539733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2408905901420710310052977 1806679426065532732539733)
            ·
              refine ⟨10586012262102730854725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1806679426065532732539733 10586012262102730854725)
              ·
                rfl

theorem cell23_1669911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 9].length) (baseStart_1669911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669911 prefixEnd_1669911 := by exact prefixLift 1669911
  have htrace : WordTrace (prefixWord ++ tailWord_1669911) baseStart_1669911 baseEnd_1669911 := by
    simpa [prefixWord, tailWord_1669911, baseEnd_1669911] using wordTrace_append hprefix tailTrace_1669911
  have hstable : (prefixWord ++ tailWord_1669911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669911).length < 2 ^ (prefixWord ++ tailWord_1669911).sum := by decide
  have hdescent : baseEnd_1669911 < baseStart_1669911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669922 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_1669922 : Nat := 118140960795 + 1669922 * 2 ^ 59
def prefixEnd_1669922 : Nat := 4983230072969 + 3 ^ 40 * 1669922 * 2
def baseEnd_1669922 : Nat := 857472641517520656195175

theorem tailTrace_1669922 : CollatzResearch.WordTrace tailWord_1669922 prefixEnd_1669922 857472641517520656195175 := by
  unfold tailWord_1669922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226764764041317204195005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40604706037443512544520013 15226764764041317204195005)
  ·
    refine ⟨5710036786515493951573127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15226764764041317204195005 5710036786515493951573127)
    ·
      refine ⟨8565055179773240927359691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5710036786515493951573127 8565055179773240927359691)
      ·
        refine ⟨12847582769659861391039537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8565055179773240927359691 12847582769659861391039537)
        ·
          refine ⟨9635687077244896043279653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12847582769659861391039537 9635687077244896043279653)
          ·
            refine ⟨1806691326983418008114935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9635687077244896043279653 1806691326983418008114935)
            ·
              refine ⟨2710036990475127012172403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806691326983418008114935 2710036990475127012172403)
              ·
                refine ⟨4065055485712690518258605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710036990475127012172403 4065055485712690518258605)
                ·
                  refine ⟨1524395807142258944346977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4065055485712690518258605 1524395807142258944346977)
                  ·
                    refine ⟨1143296855356694208260233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1524395807142258944346977 1143296855356694208260233)
                    ·
                      refine ⟨857472641517520656195175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143296855356694208260233 857472641517520656195175)
                      ·
                        rfl

theorem cell23_1669922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_1669922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669922 prefixEnd_1669922 := by exact prefixLift 1669922
  have htrace : WordTrace (prefixWord ++ tailWord_1669922) baseStart_1669922 baseEnd_1669922 := by
    simpa [prefixWord, tailWord_1669922, baseEnd_1669922] using wordTrace_append hprefix tailTrace_1669922
  have hstable : (prefixWord ++ tailWord_1669922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669922).length < 2 ^ (prefixWord ++ tailWord_1669922).sum := by decide
  have hdescent : baseEnd_1669922 < baseStart_1669922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669972 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_1669972 : Nat := 118140960795 + 1669972 * 2 ^ 59
def prefixEnd_1669972 : Nat := 4983230072969 + 3 ^ 40 * 1669972 * 2
def baseEnd_1669972 : Nat := 857498315550245460569945

theorem tailTrace_1669972 : CollatzResearch.WordTrace tailWord_1669972 prefixEnd_1669972 857498315550245460569945 := by
  unfold tailWord_1669972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30454441352992063678050085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40605921803989418237400113 30454441352992063678050085)
  ·
    refine ⟨5710207753686011939634391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30454441352992063678050085 5710207753686011939634391)
    ·
      refine ⟨8565311630529017909451587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5710207753686011939634391 8565311630529017909451587)
      ·
        refine ⟨12847967445793526864177381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8565311630529017909451587 12847967445793526864177381)
        ·
          refine ⟨2408993896086286287033259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12847967445793526864177381 2408993896086286287033259)
          ·
            refine ⟨3613490844129429430549889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408993896086286287033259 3613490844129429430549889)
            ·
              refine ⟨2710118133097072072912417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613490844129429430549889 2710118133097072072912417)
              ·
                refine ⟨2032588599822804054684313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710118133097072072912417 2032588599822804054684313)
                ·
                  refine ⟨1524441449867103041013235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032588599822804054684313 1524441449867103041013235)
                  ·
                    refine ⟨2286662174800654561519853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1524441449867103041013235 2286662174800654561519853)
                    ·
                      refine ⟨857498315550245460569945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2286662174800654561519853 857498315550245460569945)
                      ·
                        rfl

theorem cell23_1669972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_1669972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669972 prefixEnd_1669972 := by exact prefixLift 1669972
  have htrace : WordTrace (prefixWord ++ tailWord_1669972) baseStart_1669972 baseEnd_1669972 := by
    simpa [prefixWord, tailWord_1669972, baseEnd_1669972] using wordTrace_append hprefix tailTrace_1669972
  have hstable : (prefixWord ++ tailWord_1669972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669972).length < 2 ^ (prefixWord ++ tailWord_1669972).sum := by decide
  have hdescent : baseEnd_1669972 < baseStart_1669972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669991 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1669991 : Nat := 118140960795 + 1669991 * 2 ^ 59
def prefixEnd_1669991 : Nat := 4983230072969 + 3 ^ 40 * 1669991 * 2
def baseEnd_1669991 : Nat := 857508071682680886232357

theorem tailTrace_1669991 : CollatzResearch.WordTrace tailWord_1669991 prefixEnd_1669991 857508071682680886232357 := by
  unfold tailWord_1669991
  simp only [CollatzResearch.WordTrace]
  refine ⟨60909575692915293601041827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40606383795276862400694551 60909575692915293601041827)
  ·
    refine ⟨91364363539372940401562741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60909575692915293601041827 91364363539372940401562741)
    ·
      refine ⟨8565409081816213162646507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91364363539372940401562741 8565409081816213162646507)
      ·
        refine ⟨12848113622724319743969761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8565409081816213162646507 12848113622724319743969761)
        ·
          refine ⟨9636085217043239807977321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12848113622724319743969761 9636085217043239807977321)
          ·
            refine ⟨7227063912782429855982991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9636085217043239807977321 7227063912782429855982991)
            ·
              refine ⟨10840595869173644783974487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7227063912782429855982991 10840595869173644783974487)
              ·
                refine ⟨16260893803760467175961731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10840595869173644783974487 16260893803760467175961731)
                ·
                  refine ⟨24391340705640700763942597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16260893803760467175961731 24391340705640700763942597)
                  ·
                    refine ⟨4573376382307631393239237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24391340705640700763942597 4573376382307631393239237)
                    ·
                      refine ⟨857508071682680886232357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4573376382307631393239237 857508071682680886232357)
                      ·
                        rfl

theorem cell23_1669991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1669991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669991 prefixEnd_1669991 := by exact prefixLift 1669991
  have htrace : WordTrace (prefixWord ++ tailWord_1669991) baseStart_1669991 baseEnd_1669991 := by
    simpa [prefixWord, tailWord_1669991, baseEnd_1669991] using wordTrace_append hprefix tailTrace_1669991
  have hstable : (prefixWord ++ tailWord_1669991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669991).length < 2 ^ (prefixWord ++ tailWord_1669991).sum := by decide
  have hdescent : baseEnd_1669991 < baseStart_1669991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669995 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 2, 2, 2]
def baseStart_1669995 : Nat := 118140960795 + 1669995 * 2 ^ 59
def prefixEnd_1669995 : Nat := 4983230072969 + 3 ^ 40 * 1669995 * 2
def baseEnd_1669995 : Nat := 857510125605298870582339

theorem tailTrace_1669995 : CollatzResearch.WordTrace tailWord_1669995 prefixEnd_1669995 857510125605298870582339 := by
  unfold tailWord_1669995
  simp only [CollatzResearch.WordTrace]
  refine ⟨60909721584900802284187439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40606481056600534856124959 60909721584900802284187439)
  ·
    refine ⟨91364582377351203426281159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60909721584900802284187439 91364582377351203426281159)
    ·
      refine ⟨137046873566026805139421739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91364582377351203426281159 137046873566026805139421739)
      ·
        refine ⟨205570310349040207709132609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137046873566026805139421739 205570310349040207709132609)
        ·
          refine ⟨154177732761780155781849457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205570310349040207709132609 154177732761780155781849457)
          ·
            refine ⟨115633299571335116836387093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154177732761780155781849457 115633299571335116836387093)
            ·
              refine ⟨5420310917406333601705645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115633299571335116836387093 5420310917406333601705645)
              ·
                refine ⟨2032616594027375100639617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5420310917406333601705645 2032616594027375100639617)
                ·
                  refine ⟨1524462445520531325479713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032616594027375100639617 1524462445520531325479713)
                  ·
                    refine ⟨1143346834140398494109785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1524462445520531325479713 1143346834140398494109785)
                    ·
                      refine ⟨857510125605298870582339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143346834140398494109785 857510125605298870582339)
                      ·
                        rfl

theorem cell23_1669995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 2, 2].length) (baseStart_1669995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1669995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1669995 prefixEnd_1669995 := by exact prefixLift 1669995
  have htrace : WordTrace (prefixWord ++ tailWord_1669995) baseStart_1669995 baseEnd_1669995 := by
    simpa [prefixWord, tailWord_1669995, baseEnd_1669995] using wordTrace_append hprefix tailTrace_1669995
  have hstable : (prefixWord ++ tailWord_1669995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669995).length < 2 ^ (prefixWord ++ tailWord_1669995).sum := by decide
  have hdescent : baseEnd_1669995 < baseStart_1669995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670001 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 7]
def baseStart_1670001 : Nat := 118140960795 + 1670001 * 2 ^ 59
def prefixEnd_1670001 : Nat := 4983230072969 + 3 ^ 40 * 1670001 * 2
def baseEnd_1670001 : Nat := 95279245165469538567479

theorem tailTrace_1670001 : CollatzResearch.WordTrace tailWord_1670001 prefixEnd_1670001 95279245165469538567479 := by
  unfold tailWord_1670001
  simp only [CollatzResearch.WordTrace]
  refine ⟨60909940422879065308905857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40606626948586043539270571 60909940422879065308905857)
  ·
    refine ⟨45682455317159298981679393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60909940422879065308905857 45682455317159298981679393)
    ·
      refine ⟨34261841487869474236259545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45682455317159298981679393 34261841487869474236259545)
      ·
        refine ⟨25696381115902105677194659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34261841487869474236259545 25696381115902105677194659)
        ·
          refine ⟨38544571673853158515791989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25696381115902105677194659 38544571673853158515791989)
          ·
            refine ⟨3613553594423733610855499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38544571673853158515791989 3613553594423733610855499)
            ·
              refine ⟨5420330391635600416283249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613553594423733610855499 5420330391635600416283249)
              ·
                refine ⟨4065247793726700312212437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5420330391635600416283249 4065247793726700312212437)
                ·
                  refine ⟨95279245165469538567479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4065247793726700312212437 95279245165469538567479)
                  ·
                    rfl

theorem cell23_1670001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 7].length) (baseStart_1670001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670001 prefixEnd_1670001 := by exact prefixLift 1670001
  have htrace : WordTrace (prefixWord ++ tailWord_1670001) baseStart_1670001 baseEnd_1670001 := by
    simpa [prefixWord, tailWord_1670001, baseEnd_1670001] using wordTrace_append hprefix tailTrace_1670001
  have hstable : (prefixWord ++ tailWord_1670001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670001).length < 2 ^ (prefixWord ++ tailWord_1670001).sum := by decide
  have hdescent : baseEnd_1670001 < baseStart_1670001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670051 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1670051 : Nat := 118140960795 + 1670051 * 2 ^ 59
def prefixEnd_1670051 : Nat := 4983230072969 + 3 ^ 40 * 1670051 * 2
def baseEnd_1670051 : Nat := 857538880521950651482081

theorem tailTrace_1670051 : CollatzResearch.WordTrace tailWord_1670051 prefixEnd_1670051 857538880521950651482081 := by
  unfold tailWord_1670051
  simp only [CollatzResearch.WordTrace]
  refine ⟨60911764072697923848226007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40607842715131949232150671 60911764072697923848226007)
  ·
    refine ⟨91367646109046885772339011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60911764072697923848226007 91367646109046885772339011)
    ·
      refine ⟨137051469163570328658508517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91367646109046885772339011 137051469163570328658508517)
      ·
        refine ⟨25697150468169436623470347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137051469163570328658508517 25697150468169436623470347)
        ·
          refine ⟨38545725702254154935205521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25697150468169436623470347 38545725702254154935205521)
          ·
            refine ⟨28909294276690616201404141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38545725702254154935205521 28909294276690616201404141)
            ·
              refine ⟨10840985353758981075526553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28909294276690616201404141 10840985353758981075526553)
              ·
                refine ⟨8130739015319235806644915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10840985353758981075526553 8130739015319235806644915)
                ·
                  refine ⟨12196108522978853709967373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8130739015319235806644915 12196108522978853709967373)
                  ·
                    refine ⟨4573540696117070141237765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12196108522978853709967373 4573540696117070141237765)
                    ·
                      refine ⟨857538880521950651482081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4573540696117070141237765 857538880521950651482081)
                      ·
                        rfl

theorem cell23_1670051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1670051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670051 prefixEnd_1670051 := by exact prefixLift 1670051
  have htrace : WordTrace (prefixWord ++ tailWord_1670051) baseStart_1670051 baseEnd_1670051 := by
    simpa [prefixWord, tailWord_1670051, baseEnd_1670051] using wordTrace_append hprefix tailTrace_1670051
  have hstable : (prefixWord ++ tailWord_1670051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670051).length < 2 ^ (prefixWord ++ tailWord_1670051).sum := by decide
  have hdescent : baseEnd_1670051 < baseStart_1670051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670086 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1670086 : Nat := 118140960795 + 1670086 * 2 ^ 59
def prefixEnd_1670086 : Nat := 4983230072969 + 3 ^ 40 * 1670086 * 2
def baseEnd_1670086 : Nat := 95284094704984223838269

theorem tailTrace_1670086 : CollatzResearch.WordTrace tailWord_1670086 prefixEnd_1670086 95284094704984223838269 := by
  unfold tailWord_1670086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903532519611597650804691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40608693751714083217166741 1903532519611597650804691)
  ·
    refine ⟨2855298779417396476207037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1903532519611597650804691 2855298779417396476207037)
    ·
      refine ⟨1070737042281523678577639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2855298779417396476207037 1070737042281523678577639)
      ·
        refine ⟨1606105563422285517866459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070737042281523678577639 1606105563422285517866459)
        ·
          refine ⟨2409158345133428276799689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606105563422285517866459 2409158345133428276799689)
          ·
            refine ⟨1806868758850071207599767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2409158345133428276799689 1806868758850071207599767)
            ·
              refine ⟨2710303138275106811399651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806868758850071207599767 2710303138275106811399651)
              ·
                refine ⟨4065454707412660217099477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710303138275106811399651 4065454707412660217099477)
                ·
                  refine ⟨95284094704984223838269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4065454707412660217099477 95284094704984223838269)
                  ·
                    rfl

theorem cell23_1670086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1670086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670086 prefixEnd_1670086 := by exact prefixLift 1670086
  have htrace : WordTrace (prefixWord ++ tailWord_1670086) baseStart_1670086 baseEnd_1670086 := by
    simpa [prefixWord, tailWord_1670086, baseEnd_1670086] using wordTrace_append hprefix tailTrace_1670086
  have hstable : (prefixWord ++ tailWord_1670086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670086).length < 2 ^ (prefixWord ++ tailWord_1670086).sum := by decide
  have hdescent : baseEnd_1670086 < baseStart_1670086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670091 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 8]
def baseStart_1670091 : Nat := 118140960795 + 1670091 * 2 ^ 59
def prefixEnd_1670091 : Nat := 4983230072969 + 3 ^ 40 * 1670091 * 2
def baseEnd_1670091 : Nat := 95284379972014499442433

theorem tailTrace_1670091 : CollatzResearch.WordTrace tailWord_1670091 prefixEnd_1670091 95284379972014499442433 := by
  unfold tailWord_1670091
  simp only [CollatzResearch.WordTrace]
  refine ⟨60913222992553010679682127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40608815328368673786454751 60913222992553010679682127)
  ·
    refine ⟨91369834488829516019523191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60913222992553010679682127 91369834488829516019523191)
    ·
      refine ⟨137054751733244274029284787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91369834488829516019523191 137054751733244274029284787)
      ·
        refine ⟨205582127599866411043927181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137054751733244274029284787 205582127599866411043927181)
        ·
          refine ⟨77093297849949904141472693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205582127599866411043927181 77093297849949904141472693)
          ·
            refine ⟨7227496673432803513263065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77093297849949904141472693 7227496673432803513263065)
            ·
              refine ⟨5420622505074602634947299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7227496673432803513263065 5420622505074602634947299)
              ·
                refine ⟨8130933757611903952420949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5420622505074602634947299 8130933757611903952420949)
                ·
                  refine ⟨95284379972014499442433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8130933757611903952420949 95284379972014499442433)
                  ·
                    rfl

theorem cell23_1670091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 8].length) (baseStart_1670091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670091 prefixEnd_1670091 := by exact prefixLift 1670091
  have htrace : WordTrace (prefixWord ++ tailWord_1670091) baseStart_1670091 baseEnd_1670091 := by
    simpa [prefixWord, tailWord_1670091, baseEnd_1670091] using wordTrace_append hprefix tailTrace_1670091
  have hstable : (prefixWord ++ tailWord_1670091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670091).length < 2 ^ (prefixWord ++ tailWord_1670091).sum := by decide
  have hdescent : baseEnd_1670091 < baseStart_1670091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670095 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 3, 4]
def baseStart_1670095 : Nat := 118140960795 + 1670095 * 2 ^ 59
def prefixEnd_1670095 : Nat := 4983230072969 + 3 ^ 40 * 1670095 * 2
def baseEnd_1670095 : Nat := 285853824556916159777293

theorem tailTrace_1670095 : CollatzResearch.WordTrace tailWord_1670095 prefixEnd_1670095 285853824556916159777293 := by
  unfold tailWord_1670095
  simp only [CollatzResearch.WordTrace]
  refine ⟨60913368884538519362827739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40608912589692346241885159 60913368884538519362827739)
  ·
    refine ⟨91370053326807779044241609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60913368884538519362827739 91370053326807779044241609)
    ·
      refine ⟨68527539995105834283181207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91370053326807779044241609 68527539995105834283181207)
      ·
        refine ⟨102791309992658751424771811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68527539995105834283181207 102791309992658751424771811)
        ·
          refine ⟨154186964988988127137157717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102791309992658751424771811 154186964988988127137157717)
          ·
            refine ⟨1806878495964704614888567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 154186964988988127137157717 1806878495964704614888567)
            ·
              refine ⟨2710317743947056922332851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806878495964704614888567 2710317743947056922332851)
              ·
                refine ⟨4065476615920585383499277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710317743947056922332851 4065476615920585383499277)
                ·
                  refine ⟨1524553730970219518812229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4065476615920585383499277 1524553730970219518812229)
                  ·
                    refine ⟨285853824556916159777293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524553730970219518812229 285853824556916159777293)
                    ·
                      rfl

theorem cell23_1670095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 4].length) (baseStart_1670095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670095 prefixEnd_1670095 := by exact prefixLift 1670095
  have htrace : WordTrace (prefixWord ++ tailWord_1670095) baseStart_1670095 baseEnd_1670095 := by
    simpa [prefixWord, tailWord_1670095, baseEnd_1670095] using wordTrace_append hprefix tailTrace_1670095
  have hstable : (prefixWord ++ tailWord_1670095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670095).length < 2 ^ (prefixWord ++ tailWord_1670095).sum := by decide
  have hdescent : baseEnd_1670095 < baseStart_1670095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670138 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_1670138 : Nat := 118140960795 + 1670138 * 2 ^ 59
def prefixEnd_1670138 : Nat := 4983230072969 + 3 ^ 40 * 1670138 * 2
def baseEnd_1670138 : Nat := 285861184446297270364727

theorem tailTrace_1670138 : CollatzResearch.WordTrace tailWord_1670138 prefixEnd_1670138 285861184446297270364727 := by
  unfold tailWord_1670138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15228734305845684426660767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40609958148921825137762045 15228734305845684426660767)
  ·
    refine ⟨22843101458768526639991151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15228734305845684426660767 22843101458768526639991151)
    ·
      refine ⟨34264652188152789959986727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22843101458768526639991151 34264652188152789959986727)
      ·
        refine ⟨51396978282229184939980091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34264652188152789959986727 51396978282229184939980091)
        ·
          refine ⟨77095467423343777409970137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51396978282229184939980091 77095467423343777409970137)
          ·
            refine ⟨57821600567507833057477603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77095467423343777409970137 57821600567507833057477603)
            ·
              refine ⟨86732400851261749586216405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57821600567507833057477603 86732400851261749586216405)
              ·
                refine ⟨2032790644951447255926947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86732400851261749586216405 2032790644951447255926947)
                ·
                  refine ⟨3049185967427170883890421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032790644951447255926947 3049185967427170883890421)
                  ·
                    refine ⟨285861184446297270364727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3049185967427170883890421 285861184446297270364727)
                    ·
                      rfl

theorem cell23_1670138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_1670138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670138 prefixEnd_1670138 := by exact prefixLift 1670138
  have htrace : WordTrace (prefixWord ++ tailWord_1670138) baseStart_1670138 baseEnd_1670138 := by
    simpa [prefixWord, tailWord_1670138, baseEnd_1670138] using wordTrace_append hprefix tailTrace_1670138
  have hstable : (prefixWord ++ tailWord_1670138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670138).length < 2 ^ (prefixWord ++ tailWord_1670138).sum := by decide
  have hdescent : baseEnd_1670138 < baseStart_1670138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670142 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_1670142 : Nat := 118140960795 + 1670142 * 2 ^ 59
def prefixEnd_1670142 : Nat := 4983230072969 + 3 ^ 40 * 1670142 * 2
def baseEnd_1670142 : Nat := 95287289695723310604907

theorem tailTrace_1670142 : CollatzResearch.WordTrace tailWord_1670142 prefixEnd_1670142 95287289695723310604907 := by
  unfold tailWord_1670142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7614385389421030798723585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40610055410245497593192453 7614385389421030798723585)
  ·
    refine ⟨5710789042065773099042689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7614385389421030798723585 5710789042065773099042689)
    ·
      refine ⟨4283091781549329824282017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5710789042065773099042689 4283091781549329824282017)
      ·
        refine ⟨3212318836161997368211513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4283091781549329824282017 3212318836161997368211513)
        ·
          refine ⟨2409239127121498026158635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3212318836161997368211513 2409239127121498026158635)
          ·
            refine ⟨3613858690682247039237953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409239127121498026158635 3613858690682247039237953)
            ·
              refine ⟨2710394018011685279428465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613858690682247039237953 2710394018011685279428465)
              ·
                refine ⟨2032795513508763959571349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710394018011685279428465 2032795513508763959571349)
                ·
                  refine ⟨95287289695723310604907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2032795513508763959571349 95287289695723310604907)
                  ·
                    rfl

theorem cell23_1670142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_1670142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670142 prefixEnd_1670142 := by exact prefixLift 1670142
  have htrace : WordTrace (prefixWord ++ tailWord_1670142) baseStart_1670142 baseEnd_1670142 := by
    simpa [prefixWord, tailWord_1670142, baseEnd_1670142] using wordTrace_append hprefix tailTrace_1670142
  have hstable : (prefixWord ++ tailWord_1670142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670142).length < 2 ^ (prefixWord ++ tailWord_1670142).sum := by decide
  have hdescent : baseEnd_1670142 < baseStart_1670142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670146 : List Nat := [3, 4, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1670146 : Nat := 118140960795 + 1670146 * 2 ^ 59
def prefixEnd_1670146 : Nat := 4983230072969 + 3 ^ 40 * 1670146 * 2
def baseEnd_1670146 : Nat := 285862553728042593264715

theorem tailTrace_1670146 : CollatzResearch.WordTrace tailWord_1670146 prefixEnd_1670146 285862553728042593264715 := by
  unfold tailWord_1670146
  simp only [CollatzResearch.WordTrace]
  refine ⟨15228807251838438768233573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40610152671569170048622861 15228807251838438768233573)
  ·
    refine ⟨2855401359719707269043795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15228807251838438768233573 2855401359719707269043795)
    ·
      refine ⟨4283102039579560903565693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2855401359719707269043795 4283102039579560903565693)
      ·
        refine ⟨1606163264842335338837135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4283102039579560903565693 1606163264842335338837135)
        ·
          refine ⟨2409244897263503008255703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606163264842335338837135 2409244897263503008255703)
          ·
            refine ⟨3613867345895254512383555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409244897263503008255703 3613867345895254512383555)
            ·
              refine ⟨5420801018842881768575333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613867345895254512383555 5420801018842881768575333)
              ·
                refine ⟨1016400191033040331607875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5420801018842881768575333 1016400191033040331607875)
                ·
                  refine ⟨1524600286549560497411813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016400191033040331607875 1524600286549560497411813)
                  ·
                    refine ⟨285862553728042593264715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524600286549560497411813 285862553728042593264715)
                    ·
                      rfl

theorem cell23_1670146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1670146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670146 prefixEnd_1670146 := by exact prefixLift 1670146
  have htrace : WordTrace (prefixWord ++ tailWord_1670146) baseStart_1670146 baseEnd_1670146 := by
    simpa [prefixWord, tailWord_1670146, baseEnd_1670146] using wordTrace_append hprefix tailTrace_1670146
  have hstable : (prefixWord ++ tailWord_1670146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670146).length < 2 ^ (prefixWord ++ tailWord_1670146).sum := by decide
  have hdescent : baseEnd_1670146 < baseStart_1670146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670168 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 1, 6]
def baseStart_1670168 : Nat := 118140960795 + 1670168 * 2 ^ 59
def prefixEnd_1670168 : Nat := 4983230072969 + 3 ^ 40 * 1670168 * 2
def baseEnd_1670168 : Nat := 285866319252842231239681

theorem tailTrace_1670168 : CollatzResearch.WordTrace tailWord_1670168 prefixEnd_1670168 285866319252842231239681 := by
  unfold tailWord_1670168
  simp only [CollatzResearch.WordTrace]
  refine ⟨30458015706637026415117579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40610687608849368553490105 30458015706637026415117579)
  ·
    refine ⟨45687023559955539622676369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30458015706637026415117579 45687023559955539622676369)
    ·
      refine ⟨34265267669966654717007277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45687023559955539622676369 34265267669966654717007277)
      ·
        refine ⟨12849475376237495518877729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34265267669966654717007277 12849475376237495518877729)
        ·
          refine ⟨9637106532178121639158297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12849475376237495518877729 9637106532178121639158297)
          ·
            refine ⟨7227829899133591229368723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9637106532178121639158297 7227829899133591229368723)
            ·
              refine ⟨10841744848700386844053085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7227829899133591229368723 10841744848700386844053085)
              ·
                refine ⟨4065654318262645066519907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10841744848700386844053085 4065654318262645066519907)
                ·
                  refine ⟨6098481477393967599779861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065654318262645066519907 6098481477393967599779861)
                  ·
                    refine ⟨285866319252842231239681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6098481477393967599779861 285866319252842231239681)
                    ·
                      rfl

theorem cell23_1670168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_1670168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670168 prefixEnd_1670168 := by exact prefixLift 1670168
  have htrace : WordTrace (prefixWord ++ tailWord_1670168) baseStart_1670168 baseEnd_1670168 := by
    simpa [prefixWord, tailWord_1670168, baseEnd_1670168] using wordTrace_append hprefix tailTrace_1670168
  have hstable : (prefixWord ++ tailWord_1670168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670168).length < 2 ^ (prefixWord ++ tailWord_1670168).sum := by decide
  have hdescent : baseEnd_1670168 < baseStart_1670168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670171 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 6]
def baseStart_1670171 : Nat := 118140960795 + 1670171 * 2 ^ 59
def prefixEnd_1670171 : Nat := 4983230072969 + 3 ^ 40 * 1670171 * 2
def baseEnd_1670171 : Nat := 857600498200490181981529

theorem tailTrace_1670171 : CollatzResearch.WordTrace tailWord_1670171 prefixEnd_1670171 857600498200490181981529 := by
  unfold tailWord_1670171
  simp only [CollatzResearch.WordTrace]
  refine ⟨60916140832263184342594367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40610760554842122895062911 60916140832263184342594367)
  ·
    refine ⟨91374211248394776513891551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60916140832263184342594367 91374211248394776513891551)
    ·
      refine ⟨137061316872592164770837327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91374211248394776513891551 137061316872592164770837327)
      ·
        refine ⟨205591975308888247156255991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137061316872592164770837327 205591975308888247156255991)
        ·
          refine ⟨308387962963332370734383987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205591975308888247156255991 308387962963332370734383987)
          ·
            refine ⟨462581944444998556101575981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308387962963332370734383987 462581944444998556101575981)
            ·
              refine ⟨173468229166874458538090993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462581944444998556101575981 173468229166874458538090993)
              ·
                refine ⟨130101171875155843903568245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173468229166874458538090993 130101171875155843903568245)
                ·
                  refine ⟨12196984863295860365959523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130101171875155843903568245 12196984863295860365959523)
                  ·
                    refine ⟨18295477294943790548939285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12196984863295860365959523 18295477294943790548939285)
                    ·
                      refine ⟨857600498200490181981529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18295477294943790548939285 857600498200490181981529)
                      ·
                        rfl

theorem cell23_1670171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_1670171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670171 prefixEnd_1670171 := by exact prefixLift 1670171
  have htrace : WordTrace (prefixWord ++ tailWord_1670171) baseStart_1670171 baseEnd_1670171 := by
    simpa [prefixWord, tailWord_1670171, baseEnd_1670171] using wordTrace_append hprefix tailTrace_1670171
  have hstable : (prefixWord ++ tailWord_1670171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670171).length < 2 ^ (prefixWord ++ tailWord_1670171).sum := by decide
  have hdescent : baseEnd_1670171 < baseStart_1670171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670186 : List Nat := [3, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_1670186 : Nat := 118140960795 + 1670186 * 2 ^ 59
def prefixEnd_1670186 : Nat := 4983230072969 + 3 ^ 40 * 1670186 * 2
def baseEnd_1670186 : Nat := 857608200410307623293961

theorem tailTrace_1670186 : CollatzResearch.WordTrace tailWord_1670186 prefixEnd_1670186 857608200410307623293961 := by
  unfold tailWord_1670186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15229171981802210476097603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40611125284805894602926941 15229171981802210476097603)
  ·
    refine ⟨22843757972703315714146405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15229171981802210476097603 22843757972703315714146405)
    ·
      refine ⟨4283204619881871696402451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22843757972703315714146405 4283204619881871696402451)
      ·
        refine ⟨6424806929822807544603677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283204619881871696402451 6424806929822807544603677)
        ·
          refine ⟨2409302598683552829226379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6424806929822807544603677 2409302598683552829226379)
          ·
            refine ⟨3613953898025329243839569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409302598683552829226379 3613953898025329243839569)
            ·
              refine ⟨2710465423518996932879677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613953898025329243839569 2710465423518996932879677)
              ·
                refine ⟨1016424533819623849829879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2710465423518996932879677 1016424533819623849829879)
                ·
                  refine ⟨1524636800729435774744819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016424533819623849829879 1524636800729435774744819)
                  ·
                    refine ⟨2286955201094153662117229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1524636800729435774744819 2286955201094153662117229)
                    ·
                      refine ⟨857608200410307623293961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2286955201094153662117229 857608200410307623293961)
                      ·
                        rfl

theorem cell23_1670186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_1670186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670186 prefixEnd_1670186 := by exact prefixLift 1670186
  have htrace : WordTrace (prefixWord ++ tailWord_1670186) baseStart_1670186 baseEnd_1670186 := by
    simpa [prefixWord, tailWord_1670186, baseEnd_1670186] using wordTrace_append hprefix tailTrace_1670186
  have hstable : (prefixWord ++ tailWord_1670186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670186).length < 2 ^ (prefixWord ++ tailWord_1670186).sum := by decide
  have hdescent : baseEnd_1670186 < baseStart_1670186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670188 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_1670188 : Nat := 118140960795 + 1670188 * 2 ^ 59
def prefixEnd_1670188 : Nat := 4983230072969 + 3 ^ 40 * 1670188 * 2
def baseEnd_1670188 : Nat := 857609227371616615468951

theorem tailTrace_1670188 : CollatzResearch.WordTrace tailWord_1670188 prefixEnd_1670188 857609227371616615468951 := by
  unfold tailWord_1670188
  simp only [CollatzResearch.WordTrace]
  refine ⟨30458380436600798122981609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40611173915467730830642145 30458380436600798122981609)
  ·
    refine ⟨22843785327450598592236207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30458380436600798122981609 22843785327450598592236207)
    ·
      refine ⟨34265677991175897888354311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22843785327450598592236207 34265677991175897888354311)
      ·
        refine ⟨51398516986763846832531467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34265677991175897888354311 51398516986763846832531467)
        ·
          refine ⟨77097775480145770248797201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51398516986763846832531467 77097775480145770248797201)
          ·
            refine ⟨57823331610109327686597901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77097775480145770248797201 57823331610109327686597901)
            ·
              refine ⟨21683749353790997882474213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57823331610109327686597901 21683749353790997882474213)
              ·
                refine ⟨4065703003835812102963915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21683749353790997882474213 4065703003835812102963915)
                ·
                  refine ⟨6098554505753718154445873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065703003835812102963915 6098554505753718154445873)
                  ·
                    refine ⟨4573915879315288615834405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6098554505753718154445873 4573915879315288615834405)
                    ·
                      refine ⟨857609227371616615468951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4573915879315288615834405 857609227371616615468951)
                      ·
                        rfl

theorem cell23_1670188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_1670188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670188 prefixEnd_1670188 := by exact prefixLift 1670188
  have htrace : WordTrace (prefixWord ++ tailWord_1670188) baseStart_1670188 baseEnd_1670188 := by
    simpa [prefixWord, tailWord_1670188, baseEnd_1670188] using wordTrace_append hprefix tailTrace_1670188
  have hstable : (prefixWord ++ tailWord_1670188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670188).length < 2 ^ (prefixWord ++ tailWord_1670188).sum := by decide
  have hdescent : baseEnd_1670188 < baseStart_1670188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670191 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_1670191 : Nat := 118140960795 + 1670191 * 2 ^ 59
def prefixEnd_1670191 : Nat := 4983230072969 + 3 ^ 40 * 1670191 * 2
def baseEnd_1670191 : Nat := 857610767813580103731437

theorem tailTrace_1670191 : CollatzResearch.WordTrace tailWord_1670191 prefixEnd_1670191 857610767813580103731437 := by
  unfold tailWord_1670191
  simp only [CollatzResearch.WordTrace]
  refine ⟨60916870292190727758322427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40611246861460485172214951 60916870292190727758322427)
  ·
    refine ⟨91375305438286091637483641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60916870292190727758322427 91375305438286091637483641)
    ·
      refine ⟨68531479078714568728112731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91375305438286091637483641 68531479078714568728112731)
      ·
        refine ⟨102797218618071853092169097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68531479078714568728112731 102797218618071853092169097)
        ·
          refine ⟨77097913963553889819126823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102797218618071853092169097 77097913963553889819126823)
          ·
            refine ⟨115646870945330834728690235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77097913963553889819126823 115646870945330834728690235)
            ·
              refine ⟨173470306417996252093035353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115646870945330834728690235 173470306417996252093035353)
              ·
                refine ⟨130102729813497189069776515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173470306417996252093035353 130102729813497189069776515)
                ·
                  refine ⟨195154094720245783604664773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130102729813497189069776515 195154094720245783604664773)
                  ·
                    refine ⟨36591392760046084425874645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195154094720245783604664773 36591392760046084425874645)
                    ·
                      refine ⟨857610767813580103731437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36591392760046084425874645 857610767813580103731437)
                      ·
                        rfl

theorem cell23_1670191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_1670191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670191 prefixEnd_1670191 := by exact prefixLift 1670191
  have htrace : WordTrace (prefixWord ++ tailWord_1670191) baseStart_1670191 baseEnd_1670191 := by
    simpa [prefixWord, tailWord_1670191, baseEnd_1670191] using wordTrace_append hprefix tailTrace_1670191
  have hstable : (prefixWord ++ tailWord_1670191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670191).length < 2 ^ (prefixWord ++ tailWord_1670191).sum := by decide
  have hdescent : baseEnd_1670191 < baseStart_1670191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670225 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_1670225 : Nat := 118140960795 + 1670225 * 2 ^ 59
def prefixEnd_1670225 : Nat := 4983230072969 + 3 ^ 40 * 1670225 * 2
def baseEnd_1670225 : Nat := 857628226155832970706281

theorem tailTrace_1670225 : CollatzResearch.WordTrace tailWord_1670225 prefixEnd_1670225 857628226155832970706281 := by
  unfold tailWord_1670225
  simp only [CollatzResearch.WordTrace]
  refine ⟨60918110374067551565060129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40612073582711701043373419 60918110374067551565060129)
  ·
    refine ⟨45688582780550663673795097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60918110374067551565060129 45688582780550663673795097)
    ·
      refine ⟨34266437085412997755346323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45688582780550663673795097 34266437085412997755346323)
      ·
        refine ⟨51399655628119496633019485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34266437085412997755346323 51399655628119496633019485)
        ·
          refine ⟨19274870860544811237382307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51399655628119496633019485 19274870860544811237382307)
          ·
            refine ⟨28912306290817216856073461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19274870860544811237382307 28912306290817216856073461)
            ·
              refine ⟨2710528714764114080256887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28912306290817216856073461 2710528714764114080256887)
              ·
                refine ⟨4065793072146171120385331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710528714764114080256887 4065793072146171120385331)
                ·
                  refine ⟨6098689608219256680577997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065793072146171120385331 6098689608219256680577997)
                  ·
                    refine ⟨2287008603082221255216749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6098689608219256680577997 2287008603082221255216749)
                    ·
                      refine ⟨857628226155832970706281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2287008603082221255216749 857628226155832970706281)
                      ·
                        rfl

theorem cell23_1670225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_1670225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670225 prefixEnd_1670225 := by exact prefixLift 1670225
  have htrace : WordTrace (prefixWord ++ tailWord_1670225) baseStart_1670225 baseEnd_1670225 := by
    simpa [prefixWord, tailWord_1670225, baseEnd_1670225] using wordTrace_append hprefix tailTrace_1670225
  have hstable : (prefixWord ++ tailWord_1670225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670225).length < 2 ^ (prefixWord ++ tailWord_1670225).sum := by decide
  have hdescent : baseEnd_1670225 < baseStart_1670225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670228 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1670228 : Nat := 118140960795 + 1670228 * 2 ^ 59
def prefixEnd_1670228 : Nat := 4983230072969 + 3 ^ 40 * 1670228 * 2
def baseEnd_1670228 : Nat := 285876588865932152989589

theorem tailTrace_1670228 : CollatzResearch.WordTrace tailWord_1670228 prefixEnd_1670228 285876588865932152989589 := by
  unfold tailWord_1670228
  simp only [CollatzResearch.WordTrace]
  refine ⟨30459109896528341538709669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40612146528704455384946225 30459109896528341538709669)
  ·
    refine ⟨5711083105599064038508063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30459109896528341538709669 5711083105599064038508063)
    ·
      refine ⟨8566624658398596057762095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5711083105599064038508063 8566624658398596057762095)
      ·
        refine ⟨12849936987597894086643143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8566624658398596057762095 12849936987597894086643143)
        ·
          refine ⟨19274905481396841129964715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12849936987597894086643143 19274905481396841129964715)
          ·
            refine ⟨28912358222095261694947073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19274905481396841129964715 28912358222095261694947073)
            ·
              refine ⟨21684268666571446271210305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28912358222095261694947073 21684268666571446271210305)
              ·
                refine ⟨16263201499928584703407729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21684268666571446271210305 16263201499928584703407729)
                ·
                  refine ⟨12197401124946438527555797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16263201499928584703407729 12197401124946438527555797)
                  ·
                    refine ⟨285876588865932152989589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12197401124946438527555797 285876588865932152989589)
                    ·
                      rfl

theorem cell23_1670228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1670228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670228 prefixEnd_1670228 := by exact prefixLift 1670228
  have htrace : WordTrace (prefixWord ++ tailWord_1670228) baseStart_1670228 baseEnd_1670228 := by
    simpa [prefixWord, tailWord_1670228, baseEnd_1670228] using wordTrace_append hprefix tailTrace_1670228
  have hstable : (prefixWord ++ tailWord_1670228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670228).length < 2 ^ (prefixWord ++ tailWord_1670228).sum := by decide
  have hdescent : baseEnd_1670228 < baseStart_1670228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670252 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 1, 3, 2]
def baseStart_1670252 : Nat := 118140960795 + 1670252 * 2 ^ 59
def prefixEnd_1670252 : Nat := 4983230072969 + 3 ^ 40 * 1670252 * 2
def baseEnd_1670252 : Nat := 857642090133504365068657

theorem tailTrace_1670252 : CollatzResearch.WordTrace tailWord_1670252 prefixEnd_1670252 857642090133504365068657 := by
  unfold tailWord_1670252
  simp only [CollatzResearch.WordTrace]
  refine ⟨30459547572484867588146505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40612730096646490117528673 30459547572484867588146505)
  ·
    refine ⟨22844660679363650691109879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30459547572484867588146505 22844660679363650691109879)
    ·
      refine ⟨34266991019045476036664819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22844660679363650691109879 34266991019045476036664819)
      ·
        refine ⟨51400486528568214054997229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34266991019045476036664819 51400486528568214054997229)
        ·
          refine ⟨19275182448213080270623961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51400486528568214054997229 19275182448213080270623961)
          ·
            refine ⟨14456386836159810202967971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19275182448213080270623961 14456386836159810202967971)
            ·
              refine ⟨21684580254239715304451957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14456386836159810202967971 21684580254239715304451957)
              ·
                refine ⟨2032929398834973309792371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21684580254239715304451957 2032929398834973309792371)
                ·
                  refine ⟨3049394098252459964688557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032929398834973309792371 3049394098252459964688557)
                  ·
                    refine ⟨1143522786844672486758209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049394098252459964688557 1143522786844672486758209)
                    ·
                      refine ⟨857642090133504365068657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143522786844672486758209 857642090133504365068657)
                      ·
                        rfl

theorem cell23_1670252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_1670252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670252 prefixEnd_1670252 := by exact prefixLift 1670252
  have htrace : WordTrace (prefixWord ++ tailWord_1670252) baseStart_1670252 baseEnd_1670252 := by
    simpa [prefixWord, tailWord_1670252, baseEnd_1670252] using wordTrace_append hprefix tailTrace_1670252
  have hstable : (prefixWord ++ tailWord_1670252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670252).length < 2 ^ (prefixWord ++ tailWord_1670252).sum := by decide
  have hdescent : baseEnd_1670252 < baseStart_1670252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670268 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_1670268 : Nat := 118140960795 + 1670268 * 2 ^ 59
def prefixEnd_1670268 : Nat := 4983230072969 + 3 ^ 40 * 1670268 * 2
def baseEnd_1670268 : Nat := 857650305823976302468583

theorem tailTrace_1670268 : CollatzResearch.WordTrace tailWord_1670268 prefixEnd_1670268 857650305823976302468583 := by
  unfold tailWord_1670268
  simp only [CollatzResearch.WordTrace]
  refine ⟨30459839356455884954437729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40613119141941179939250305 30459839356455884954437729)
  ·
    refine ⟨22844879517341913715828297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30459839356455884954437729 22844879517341913715828297)
    ·
      refine ⟨17133659638006435286871223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22844879517341913715828297 17133659638006435286871223)
      ·
        refine ⟨25700489457009652930306835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17133659638006435286871223 25700489457009652930306835)
        ·
          refine ⟨38550734185514479395460253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25700489457009652930306835 38550734185514479395460253)
          ·
            refine ⟨14456525319567929773297595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38550734185514479395460253 14456525319567929773297595)
            ·
              refine ⟨21684787979351894659946393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14456525319567929773297595 21684787979351894659946393)
              ·
                refine ⟨16263590984513920994959795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21684787979351894659946393 16263590984513920994959795)
                ·
                  refine ⟨24395386476770881492439693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16263590984513920994959795 24395386476770881492439693)
                  ·
                    refine ⟨9148269928789080559664885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24395386476770881492439693 9148269928789080559664885)
                    ·
                      refine ⟨857650305823976302468583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9148269928789080559664885 857650305823976302468583)
                      ·
                        rfl

theorem cell23_1670268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_1670268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670268 prefixEnd_1670268 := by exact prefixLift 1670268
  have htrace : WordTrace (prefixWord ++ tailWord_1670268) baseStart_1670268 baseEnd_1670268 := by
    simpa [prefixWord, tailWord_1670268, baseEnd_1670268] using wordTrace_append hprefix tailTrace_1670268
  have hstable : (prefixWord ++ tailWord_1670268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670268).length < 2 ^ (prefixWord ++ tailWord_1670268).sum := by decide
  have hdescent : baseEnd_1670268 < baseStart_1670268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670270 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1670270 : Nat := 118140960795 + 1670270 * 2 ^ 59
def prefixEnd_1670270 : Nat := 4983230072969 + 3 ^ 40 * 1670270 * 2
def baseEnd_1670270 : Nat := 285883777595095098214525

theorem tailTrace_1670270 : CollatzResearch.WordTrace tailWord_1670270 prefixEnd_1670270 285883777595095098214525 := by
  unfold tailWord_1670270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7614968957363065531306033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40613167772603016166965509 7614968957363065531306033)
  ·
    refine ⟨5711226718022299148479525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7614968957363065531306033 5711226718022299148479525)
    ·
      refine ⟨1070855009629181090339911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5711226718022299148479525 1070855009629181090339911)
      ·
        refine ⟨1606282514443771635509867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070855009629181090339911 1606282514443771635509867)
        ·
          refine ⟨2409423771665657453264801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606282514443771635509867 2409423771665657453264801)
          ·
            refine ⟨1807067828749243089948601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2409423771665657453264801 1807067828749243089948601)
            ·
              refine ⟨1355300871561932317461451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807067828749243089948601 1355300871561932317461451)
              ·
                refine ⟨2032951307342898476192177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355300871561932317461451 2032951307342898476192177)
                ·
                  refine ⟨1524713480507173857144133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032951307342898476192177 1524713480507173857144133)
                  ·
                    refine ⟨285883777595095098214525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524713480507173857144133 285883777595095098214525)
                    ·
                      rfl

theorem cell23_1670270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1670270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670270 prefixEnd_1670270 := by exact prefixLift 1670270
  have htrace : WordTrace (prefixWord ++ tailWord_1670270) baseStart_1670270 baseEnd_1670270 := by
    simpa [prefixWord, tailWord_1670270, baseEnd_1670270] using wordTrace_append hprefix tailTrace_1670270
  have hstable : (prefixWord ++ tailWord_1670270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670270).length < 2 ^ (prefixWord ++ tailWord_1670270).sum := by decide
  have hdescent : baseEnd_1670270 < baseStart_1670270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670276 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_1670276 : Nat := 118140960795 + 1670276 * 2 ^ 59
def prefixEnd_1670276 : Nat := 4983230072969 + 3 ^ 40 * 1670276 * 2
def baseEnd_1670276 : Nat := 857654413669212271168547

theorem tailTrace_1670276 : CollatzResearch.WordTrace tailWord_1670276 prefixEnd_1670276 857654413669212271168547 := by
  unfold tailWord_1670276
  simp only [CollatzResearch.WordTrace]
  refine ⟨30459985248441393637583341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40613313664588524850111121 30459985248441393637583341)
  ·
    refine ⟨11422494468165522614093753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30459985248441393637583341 11422494468165522614093753)
    ·
      refine ⟨8566870851124141960570315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11422494468165522614093753 8566870851124141960570315)
      ·
        refine ⟨12850306276686212940855473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8566870851124141960570315 12850306276686212940855473)
        ·
          refine ⟨9637729707514659705641605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12850306276686212940855473 9637729707514659705641605)
          ·
            refine ⟨1807074320158998694807801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9637729707514659705641605 1807074320158998694807801)
            ·
              refine ⟨1355305740119249021105851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807074320158998694807801 1355305740119249021105851)
              ·
                refine ⟨2032958610178873531658777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355305740119249021105851 2032958610178873531658777)
                ·
                  refine ⟨1524718957634155148744083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032958610178873531658777 1524718957634155148744083)
                  ·
                    refine ⟨2287078436451232723116125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1524718957634155148744083 2287078436451232723116125)
                    ·
                      refine ⟨857654413669212271168547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2287078436451232723116125 857654413669212271168547)
                      ·
                        rfl

theorem cell23_1670276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_1670276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670276 prefixEnd_1670276 := by exact prefixLift 1670276
  have htrace : WordTrace (prefixWord ++ tailWord_1670276) baseStart_1670276 baseEnd_1670276 := by
    simpa [prefixWord, tailWord_1670276, baseEnd_1670276] using wordTrace_append hprefix tailTrace_1670276
  have hstable : (prefixWord ++ tailWord_1670276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670276).length < 2 ^ (prefixWord ++ tailWord_1670276).sum := by decide
  have hdescent : baseEnd_1670276 < baseStart_1670276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670282 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_1670282 : Nat := 118140960795 + 1670282 * 2 ^ 59
def prefixEnd_1670282 : Nat := 4983230072969 + 3 ^ 40 * 1670282 * 2
def baseEnd_1670282 : Nat := 857657494553139247693519

theorem tailTrace_1670282 : CollatzResearch.WordTrace tailWord_1670282 prefixEnd_1670282 857657494553139247693519 := by
  unfold tailWord_1670282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15230047333715262574971275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40613459556574033533256733 15230047333715262574971275)
  ·
    refine ⟨22845071000572893862456913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15230047333715262574971275 22845071000572893862456913)
    ·
      refine ⟨17133803250429670396842685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22845071000572893862456913 17133803250429670396842685)
      ·
        refine ⟨6425176218911126398816007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17133803250429670396842685 6425176218911126398816007)
        ·
          refine ⟨9637764328366689598224011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6425176218911126398816007 9637764328366689598224011)
          ·
            refine ⟨14456646492550034397336017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9637764328366689598224011 14456646492550034397336017)
            ·
              refine ⟨10842484869412525798002013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14456646492550034397336017 10842484869412525798002013)
              ·
                refine ⟨4065931826029697174250755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10842484869412525798002013 4065931826029697174250755)
                ·
                  refine ⟨6098897739044545761376133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065931826029697174250755 6098897739044545761376133)
                  ·
                    refine ⟨1143543326070852330258025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6098897739044545761376133 1143543326070852330258025)
                    ·
                      refine ⟨857657494553139247693519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143543326070852330258025 857657494553139247693519)
                      ·
                        rfl

theorem cell23_1670282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_1670282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670282 prefixEnd_1670282 := by exact prefixLift 1670282
  have htrace : WordTrace (prefixWord ++ tailWord_1670282) baseStart_1670282 baseEnd_1670282 := by
    simpa [prefixWord, tailWord_1670282, baseEnd_1670282] using wordTrace_append hprefix tailTrace_1670282
  have hstable : (prefixWord ++ tailWord_1670282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670282).length < 2 ^ (prefixWord ++ tailWord_1670282).sum := by decide
  have hdescent : baseEnd_1670282 < baseStart_1670282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670286 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_1670286 : Nat := 118140960795 + 1670286 * 2 ^ 59
def prefixEnd_1670286 : Nat := 4983230072969 + 3 ^ 40 * 1670286 * 2
def baseEnd_1670286 : Nat := 857659548475757232043501

theorem tailTrace_1670286 : CollatzResearch.WordTrace tailWord_1670286 prefixEnd_1670286 857659548475757232043501 := by
  unfold tailWord_1670286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615041903355819872878839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40613556817897705988687141 7615041903355819872878839)
  ·
    refine ⟨11422562855033729809318259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7615041903355819872878839 11422562855033729809318259)
    ·
      refine ⟨17133844282550594713977389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11422562855033729809318259 17133844282550594713977389)
      ·
        refine ⟨6425191605956473017741521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17133844282550594713977389 6425191605956473017741521)
        ·
          refine ⟨4818893704467354763306141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6425191605956473017741521 4818893704467354763306141)
          ·
            refine ⟨1807085139175258036239803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4818893704467354763306141 1807085139175258036239803)
            ·
              refine ⟨2710627708762887054359705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807085139175258036239803 2710627708762887054359705)
              ·
                refine ⟨2032970781572165290769779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710627708762887054359705 2032970781572165290769779)
                ·
                  refine ⟨3049456172358247936154669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032970781572165290769779 3049456172358247936154669)
                  ·
                    refine ⟨1143546064634342976058001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049456172358247936154669 1143546064634342976058001)
                    ·
                      refine ⟨857659548475757232043501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143546064634342976058001 857659548475757232043501)
                      ·
                        rfl

theorem cell23_1670286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_1670286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670286 prefixEnd_1670286 := by exact prefixLift 1670286
  have htrace : WordTrace (prefixWord ++ tailWord_1670286) baseStart_1670286 baseEnd_1670286 := by
    simpa [prefixWord, tailWord_1670286, baseEnd_1670286] using wordTrace_append hprefix tailTrace_1670286
  have hstable : (prefixWord ++ tailWord_1670286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670286).length < 2 ^ (prefixWord ++ tailWord_1670286).sum := by decide
  have hdescent : baseEnd_1670286 < baseStart_1670286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670302 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1670302 : Nat := 118140960795 + 1670302 * 2 ^ 59
def prefixEnd_1670302 : Nat := 4983230072969 + 3 ^ 40 * 1670302 * 2
def baseEnd_1670302 : Nat := 857667764166229169443427

theorem tailTrace_1670302 : CollatzResearch.WordTrace tailWord_1670302 prefixEnd_1670302 857667764166229169443427 := by
  unfold tailWord_1670302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615114849348574214451645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40613945863192395810408773 7615114849348574214451645)
  ·
    refine ⟨2855668068505715330419367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7615114849348574214451645 2855668068505715330419367)
    ·
      refine ⟨4283502102758572995629051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2855668068505715330419367 4283502102758572995629051)
      ·
        refine ⟨6425253154137859493443577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283502102758572995629051 6425253154137859493443577)
        ·
          refine ⟨4818939865603394620082683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6425253154137859493443577 4818939865603394620082683)
          ·
            refine ⟨7228409798405091930124025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818939865603394620082683 7228409798405091930124025)
            ·
              refine ⟨5421307348803818947593019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7228409798405091930124025 5421307348803818947593019)
              ·
                refine ⟨8131961023205728421389529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5421307348803818947593019 8131961023205728421389529)
                ·
                  refine ⟨6098970767404296316042147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8131961023205728421389529 6098970767404296316042147)
                  ·
                    refine ⟨9148456151106444474063221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6098970767404296316042147 9148456151106444474063221)
                    ·
                      refine ⟨857667764166229169443427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9148456151106444474063221 857667764166229169443427)
                      ·
                        rfl

theorem cell23_1670302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1670302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670302 prefixEnd_1670302 := by exact prefixLift 1670302
  have htrace : WordTrace (prefixWord ++ tailWord_1670302) baseStart_1670302 baseEnd_1670302 := by
    simpa [prefixWord, tailWord_1670302, baseEnd_1670302] using wordTrace_append hprefix tailTrace_1670302
  have hstable : (prefixWord ++ tailWord_1670302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670302).length < 2 ^ (prefixWord ++ tailWord_1670302).sum := by decide
  have hdescent : baseEnd_1670302 < baseStart_1670302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670322 : List Nat := [3, 2, 1, 1, 1, 5, 1, 4, 5]
def baseStart_1670322 : Nat := 118140960795 + 1670322 * 2 ^ 59
def prefixEnd_1670322 : Nat := 4983230072969 + 3 ^ 40 * 1670322 * 2
def baseEnd_1670322 : Nat := 95297559308813232354815

theorem tailTrace_1670322 : CollatzResearch.WordTrace tailWord_1670322 prefixEnd_1670322 95297559308813232354815 := by
  unfold tailWord_1670322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15230412063679034282835305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40614432169810758087560813 15230412063679034282835305)
  ·
    refine ⟨11422809047759275712126479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15230412063679034282835305 11422809047759275712126479)
    ·
      refine ⟨17134213571638913568189719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11422809047759275712126479 17134213571638913568189719)
      ·
        refine ⟨25701320357458370352284579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17134213571638913568189719 25701320357458370352284579)
        ·
          refine ⟨38551980536187555528426869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25701320357458370352284579 38551980536187555528426869)
          ·
            refine ⟨3614248175267583330790019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38551980536187555528426869 3614248175267583330790019)
            ·
              refine ⟨5421372262901374996185029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614248175267583330790019 5421372262901374996185029)
              ·
                refine ⟨1016507299294007811784693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5421372262901374996185029 1016507299294007811784693)
                ·
                  refine ⟨95297559308813232354815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016507299294007811784693 95297559308813232354815)
                  ·
                    rfl

theorem cell23_1670322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_1670322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670322 prefixEnd_1670322 := by exact prefixLift 1670322
  have htrace : WordTrace (prefixWord ++ tailWord_1670322) baseStart_1670322 baseEnd_1670322 := by
    simpa [prefixWord, tailWord_1670322, baseEnd_1670322] using wordTrace_append hprefix tailTrace_1670322
  have hstable : (prefixWord ++ tailWord_1670322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670322).length < 2 ^ (prefixWord ++ tailWord_1670322).sum := by decide
  have hdescent : baseEnd_1670322 < baseStart_1670322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670328 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_1670328 : Nat := 118140960795 + 1670328 * 2 ^ 59
def prefixEnd_1670328 : Nat := 4983230072969 + 3 ^ 40 * 1670328 * 2
def baseEnd_1670328 : Nat := 857681114663246067718307

theorem tailTrace_1670328 : CollatzResearch.WordTrace tailWord_1670328 prefixEnd_1670328 857681114663246067718307 := by
  unfold tailWord_1670328
  simp only [CollatzResearch.WordTrace]
  refine ⟨30460933546347200078029819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40614578061796266770706425 30460933546347200078029819)
  ·
    refine ⟨45691400319520800117044729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30460933546347200078029819 45691400319520800117044729)
    ·
      refine ⟨34268550239640600087783547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45691400319520800117044729 34268550239640600087783547)
      ·
        refine ⟨51402825359460900131675321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34268550239640600087783547 51402825359460900131675321)
        ·
          refine ⟨38552119019595675098756491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51402825359460900131675321 38552119019595675098756491)
          ·
            refine ⟨57828178529393512648134737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38552119019595675098756491 57828178529393512648134737)
            ·
              refine ⟨43371133897045134486101053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57828178529393512648134737 43371133897045134486101053)
              ·
                refine ⟨16264175211391925432287895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43371133897045134486101053 16264175211391925432287895)
                ·
                  refine ⟨24396262817087888148431843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16264175211391925432287895 24396262817087888148431843)
                  ·
                    refine ⟨36594394225631832222647765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24396262817087888148431843 36594394225631832222647765)
                    ·
                      refine ⟨857681114663246067718307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36594394225631832222647765 857681114663246067718307)
                      ·
                        rfl

theorem cell23_1670328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_1670328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670328 prefixEnd_1670328 := by exact prefixLift 1670328
  have htrace : WordTrace (prefixWord ++ tailWord_1670328) baseStart_1670328 baseEnd_1670328 := by
    simpa [prefixWord, tailWord_1670328, baseEnd_1670328] using wordTrace_append hprefix tailTrace_1670328
  have hstable : (prefixWord ++ tailWord_1670328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670328).length < 2 ^ (prefixWord ++ tailWord_1670328).sum := by decide
  have hdescent : baseEnd_1670328 < baseStart_1670328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670332 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1670332 : Nat := 118140960795 + 1670332 * 2 ^ 59
def prefixEnd_1670332 : Nat := 4983230072969 + 3 ^ 40 * 1670332 * 2
def baseEnd_1670332 : Nat := 857683168585864052068289

theorem tailTrace_1670332 : CollatzResearch.WordTrace tailWord_1670332 prefixEnd_1670332 857683168585864052068289 := by
  unfold tailWord_1670332
  simp only [CollatzResearch.WordTrace]
  refine ⟨30461006492339954419602625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40614675323119939226136833 30461006492339954419602625)
  ·
    refine ⟨22845754869254965814701969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30461006492339954419602625 22845754869254965814701969)
    ·
      refine ⟨17134316151941224361026477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22845754869254965814701969 17134316151941224361026477)
      ·
        refine ⟨6425368556977959135384929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17134316151941224361026477 6425368556977959135384929)
        ·
          refine ⟨4819026417733469351538697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6425368556977959135384929 4819026417733469351538697)
          ·
            refine ⟨3614269813300102013654023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4819026417733469351538697 3614269813300102013654023)
            ·
              refine ⟨5421404719950153020481035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614269813300102013654023 5421404719950153020481035)
              ·
                refine ⟨8132107079925229530721553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5421404719950153020481035 8132107079925229530721553)
                ·
                  refine ⟨6099080309943922148041165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8132107079925229530721553 6099080309943922148041165)
                  ·
                    refine ⟨2287155116228970805515437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6099080309943922148041165 2287155116228970805515437)
                    ·
                      refine ⟨857683168585864052068289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2287155116228970805515437 857683168585864052068289)
                      ·
                        rfl

theorem cell23_1670332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1670332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670332 prefixEnd_1670332 := by exact prefixLift 1670332
  have htrace : WordTrace (prefixWord ++ tailWord_1670332) baseStart_1670332 baseEnd_1670332 := by
    simpa [prefixWord, tailWord_1670332, baseEnd_1670332] using wordTrace_append hprefix tailTrace_1670332
  have hstable : (prefixWord ++ tailWord_1670332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670332).length < 2 ^ (prefixWord ++ tailWord_1670332).sum := by decide
  have hdescent : baseEnd_1670332 < baseStart_1670332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670356 : List Nat := [2, 4, 1, 4, 1, 1, 2, 3, 5]
def baseStart_1670356 : Nat := 118140960795 + 1670356 * 2 ^ 59
def prefixEnd_1670356 : Nat := 4983230072969 + 3 ^ 40 * 1670356 * 2
def baseEnd_1670356 : Nat := 95299499124619106463131

theorem tailTrace_1670356 : CollatzResearch.WordTrace tailWord_1670356 prefixEnd_1670356 95299499124619106463131 := by
  unfold tailWord_1670356
  simp only [CollatzResearch.WordTrace]
  refine ⟨30461444168296480469039461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40615258891061973958719281 30461444168296480469039461)
  ·
    refine ⟨5711520781555590087944899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30461444168296480469039461 5711520781555590087944899)
    ·
      refine ⟨8567281172333385131917349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5711520781555590087944899 8567281172333385131917349)
      ·
        refine ⟨1606365219812509712234503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8567281172333385131917349 1606365219812509712234503)
        ·
          refine ⟨2409547829718764568351755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606365219812509712234503 2409547829718764568351755)
          ·
            refine ⟨3614321744578146852527633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409547829718764568351755 3614321744578146852527633)
            ·
              refine ⟨2710741308433610139395725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3614321744578146852527633 2710741308433610139395725)
              ·
                refine ⟨1016527990662603802273397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2710741308433610139395725 1016527990662603802273397)
                ·
                  refine ⟨95299499124619106463131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016527990662603802273397 95299499124619106463131)
                  ·
                    rfl

theorem cell23_1670356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_1670356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670356 prefixEnd_1670356 := by exact prefixLift 1670356
  have htrace : WordTrace (prefixWord ++ tailWord_1670356) baseStart_1670356 baseEnd_1670356 := by
    simpa [prefixWord, tailWord_1670356, baseEnd_1670356] using wordTrace_append hprefix tailTrace_1670356
  have hstable : (prefixWord ++ tailWord_1670356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670356).length < 2 ^ (prefixWord ++ tailWord_1670356).sum := by decide
  have hdescent : baseEnd_1670356 < baseStart_1670356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670372 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_1670372 : Nat := 118140960795 + 1670372 * 2 ^ 59
def prefixEnd_1670372 : Nat := 4983230072969 + 3 ^ 40 * 1670372 * 2
def baseEnd_1670372 : Nat := 857703707812043895568105

theorem tailTrace_1670372 : CollatzResearch.WordTrace tailWord_1670372 prefixEnd_1670372 857703707812043895568105 := by
  unfold tailWord_1670372
  simp only [CollatzResearch.WordTrace]
  refine ⟨30461735952267497835330685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40615647936356663780440913 30461735952267497835330685)
  ·
    refine ⟨11423150982100311688249007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30461735952267497835330685 11423150982100311688249007)
    ·
      refine ⟨17134726473150467532373511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11423150982100311688249007 17134726473150467532373511)
      ·
        refine ⟨25702089709725701298560267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17134726473150467532373511 25702089709725701298560267)
        ·
          refine ⟨38553134564588551947840401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25702089709725701298560267 38553134564588551947840401)
          ·
            refine ⟨28914850923441413960880301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38553134564588551947840401 28914850923441413960880301)
            ·
              refine ⟨10843069096290530235330113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28914850923441413960880301 10843069096290530235330113)
              ·
                refine ⟨8132301822217897676497585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10843069096290530235330113 8132301822217897676497585)
                ·
                  refine ⟨6099226366663423257373189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8132301822217897676497585 6099226366663423257373189)
                  ·
                    refine ⟨1143604943749391860757473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6099226366663423257373189 1143604943749391860757473)
                    ·
                      refine ⟨857703707812043895568105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143604943749391860757473 857703707812043895568105)
                      ·
                        rfl

theorem cell23_1670372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_1670372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670372 prefixEnd_1670372 := by exact prefixLift 1670372
  have htrace : WordTrace (prefixWord ++ tailWord_1670372) baseStart_1670372 baseEnd_1670372 := by
    simpa [prefixWord, tailWord_1670372, baseEnd_1670372] using wordTrace_append hprefix tailTrace_1670372
  have hstable : (prefixWord ++ tailWord_1670372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670372).length < 2 ^ (prefixWord ++ tailWord_1670372).sum := by decide
  have hdescent : baseEnd_1670372 < baseStart_1670372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670382 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1670382 : Nat := 118140960795 + 1670382 * 2 ^ 59
def prefixEnd_1670382 : Nat := 4983230072969 + 3 ^ 40 * 1670382 * 2
def baseEnd_1670382 : Nat := 285902947539529618814353

theorem tailTrace_1670382 : CollatzResearch.WordTrace tailWord_1670382 prefixEnd_1670382 285902947539529618814353 := by
  unfold tailWord_1670382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615479579312345922315675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40615891089665844919016933 7615479579312345922315675)
  ·
    refine ⟨11423219368968518883473513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7615479579312345922315675 11423219368968518883473513)
    ·
      refine ⟨8567414526726389162605135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11423219368968518883473513 8567414526726389162605135)
      ·
        refine ⟨12851121790089583743907703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8567414526726389162605135 12851121790089583743907703)
        ·
          refine ⟨19276682685134375615861555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12851121790089583743907703 19276682685134375615861555)
          ·
            refine ⟨28915024027701563423792333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19276682685134375615861555 28915024027701563423792333)
            ·
              refine ⟨10843134010388086283922125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28915024027701563423792333 10843134010388086283922125)
              ·
                refine ⟨4066175253895532356470797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10843134010388086283922125 4066175253895532356470797)
                ·
                  refine ⟨1524815720210824633676549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4066175253895532356470797 1524815720210824633676549)
                  ·
                    refine ⟨285902947539529618814353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524815720210824633676549 285902947539529618814353)
                    ·
                      rfl

theorem cell23_1670382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1670382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670382 prefixEnd_1670382 := by exact prefixLift 1670382
  have htrace : WordTrace (prefixWord ++ tailWord_1670382) baseStart_1670382 baseEnd_1670382 := by
    simpa [prefixWord, tailWord_1670382, baseEnd_1670382] using wordTrace_append hprefix tailTrace_1670382
  have hstable : (prefixWord ++ tailWord_1670382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670382).length < 2 ^ (prefixWord ++ tailWord_1670382).sum := by decide
  have hdescent : baseEnd_1670382 < baseStart_1670382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670405 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_1670405 : Nat := 118140960795 + 1670405 * 2 ^ 59
def prefixEnd_1670405 : Nat := 4983230072969 + 3 ^ 40 * 1670405 * 2
def baseEnd_1670405 : Nat := 857720652673642266455453

theorem tailTrace_1670405 : CollatzResearch.WordTrace tailWord_1670405 prefixEnd_1670405 857720652673642266455453 := by
  unfold tailWord_1670405
  simp only [CollatzResearch.WordTrace]
  refine ⟨60924675513415442306612669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40616450342276961537741779 60924675513415442306612669)
  ·
    refine ⟨22846753317530790864979751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60924675513415442306612669 22846753317530790864979751)
    ·
      refine ⟨34270129976296186297469627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22846753317530790864979751 34270129976296186297469627)
      ·
        refine ⟨51405194964444279446204441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34270129976296186297469627 51405194964444279446204441)
        ·
          refine ⟨38553896223333209584653331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51405194964444279446204441 38553896223333209584653331)
          ·
            refine ⟨57830844334999814376979997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38553896223333209584653331 57830844334999814376979997)
            ·
              refine ⟨21686566625624930391367499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57830844334999814376979997 21686566625624930391367499)
              ·
                refine ⟨32529849938437395587051249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21686566625624930391367499 32529849938437395587051249)
                ·
                  refine ⟨24397387453828046690288437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32529849938437395587051249 24397387453828046690288437)
                  ·
                    refine ⟨2287255073796379377214541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24397387453828046690288437 2287255073796379377214541)
                    ·
                      refine ⟨857720652673642266455453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2287255073796379377214541 857720652673642266455453)
                      ·
                        rfl

theorem cell23_1670405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_1670405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670405 prefixEnd_1670405 := by exact prefixLift 1670405
  have htrace : WordTrace (prefixWord ++ tailWord_1670405) baseStart_1670405 baseEnd_1670405 := by
    simpa [prefixWord, tailWord_1670405, baseEnd_1670405] using wordTrace_append hprefix tailTrace_1670405
  have hstable : (prefixWord ++ tailWord_1670405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670405).length < 2 ^ (prefixWord ++ tailWord_1670405).sum := by decide
  have hdescent : baseEnd_1670405 < baseStart_1670405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670485 : List Nat := [1, 3, 2, 2, 3, 12]
def baseStart_1670485 : Nat := 118140960795 + 1670485 * 2 ^ 59
def prefixEnd_1670485 : Nat := 4983230072969 + 3 ^ 40 * 1670485 * 2
def baseEnd_1670485 : Nat := 3529883667185193224095

theorem tailTrace_1670485 : CollatzResearch.WordTrace tailWord_1670485 prefixEnd_1670485 3529883667185193224095 := by
  unfold tailWord_1670485
  simp only [CollatzResearch.WordTrace]
  refine ⟨60927593353125615969524909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40618395568750410646349939 60927593353125615969524909)
  ·
    refine ⟨22847847507422105988571841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60927593353125615969524909 22847847507422105988571841)
    ·
      refine ⟨17135885630566579491428881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22847847507422105988571841 17135885630566579491428881)
      ·
        refine ⟨12851914222924934618571661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17135885630566579491428881 12851914222924934618571661)
        ·
          refine ⟨4819467833596850481964373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12851914222924934618571661 4819467833596850481964373)
          ·
            refine ⟨3529883667185193224095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4819467833596850481964373 3529883667185193224095)
            ·
              rfl

theorem cell23_1670485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 12].length) (baseStart_1670485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670485 prefixEnd_1670485 := by exact prefixLift 1670485
  have htrace : WordTrace (prefixWord ++ tailWord_1670485) baseStart_1670485 baseEnd_1670485 := by
    simpa [prefixWord, tailWord_1670485, baseEnd_1670485] using wordTrace_append hprefix tailTrace_1670485
  have hstable : (prefixWord ++ tailWord_1670485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670485).length < 2 ^ (prefixWord ++ tailWord_1670485).sum := by decide
  have hdescent : baseEnd_1670485 < baseStart_1670485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670509 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1670509 : Nat := 118140960795 + 1670509 * 2 ^ 59
def prefixEnd_1670509 : Nat := 4983230072969 + 3 ^ 40 * 1670509 * 2
def baseEnd_1670509 : Nat := 857774054661709859554975

theorem tailTrace_1670509 : CollatzResearch.WordTrace tailWord_1670509 prefixEnd_1670509 857774054661709859554975 := by
  unfold tailWord_1670509
  simp only [CollatzResearch.WordTrace]
  refine ⟨60928468705038668068398581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40618979136692445378932387 60928468705038668068398581)
  ·
    refine ⟨5712043941097375131412367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60928468705038668068398581 5712043941097375131412367)
    ·
      refine ⟨8568065911646062697118551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5712043941097375131412367 8568065911646062697118551)
      ·
        refine ⟨12852098867469094045677827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8568065911646062697118551 12852098867469094045677827)
        ·
          refine ⟨19278148301203641068516741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12852098867469094045677827 19278148301203641068516741)
          ·
            refine ⟨3614652806475682700346889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19278148301203641068516741 3614652806475682700346889)
            ·
              refine ⟨2710989604856762025260167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3614652806475682700346889 2710989604856762025260167)
              ·
                refine ⟨4066484407285143037890251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710989604856762025260167 4066484407285143037890251)
                ·
                  refine ⟨6099726610927714556835377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4066484407285143037890251 6099726610927714556835377)
                  ·
                    refine ⟨4574794958195785917626533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6099726610927714556835377 4574794958195785917626533)
                    ·
                      refine ⟨857774054661709859554975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4574794958195785917626533 857774054661709859554975)
                      ·
                        rfl

theorem cell23_1670509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1670509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670509 prefixEnd_1670509 := by exact prefixLift 1670509
  have htrace : WordTrace (prefixWord ++ tailWord_1670509) baseStart_1670509 baseEnd_1670509 := by
    simpa [prefixWord, tailWord_1670509, baseEnd_1670509] using wordTrace_append hprefix tailTrace_1670509
  have hstable : (prefixWord ++ tailWord_1670509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670509).length < 2 ^ (prefixWord ++ tailWord_1670509).sum := by decide
  have hdescent : baseEnd_1670509 < baseStart_1670509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670530 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_1670530 : Nat := 118140960795 + 1670530 * 2 ^ 59
def prefixEnd_1670530 : Nat := 4983230072969 + 3 ^ 40 * 1670530 * 2
def baseEnd_1670530 : Nat := 857784837755454277392379

theorem tailTrace_1670530 : CollatzResearch.WordTrace tailWord_1670530 prefixEnd_1670530 857784837755454277392379 := by
  unfold tailWord_1670530
  simp only [CollatzResearch.WordTrace]
  refine ⟨15232308659490647163728261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40619489758641725769942029 15232308659490647163728261)
  ·
    refine ⟨2856057873654496343199049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15232308659490647163728261 2856057873654496343199049)
    ·
      refine ⟨2142043405240872257399287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2856057873654496343199049 2142043405240872257399287)
      ·
        refine ⟨3213065107861308386098931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142043405240872257399287 3213065107861308386098931)
        ·
          refine ⟨4819597661791962579148397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213065107861308386098931 4819597661791962579148397)
          ·
            refine ⟨1807349123171985967180649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4819597661791962579148397 1807349123171985967180649)
            ·
              refine ⟨1355511842378989475385487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807349123171985967180649 1355511842378989475385487)
              ·
                refine ⟨2033267763568484213078231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355511842378989475385487 2033267763568484213078231)
                ·
                  refine ⟨3049901645352726319617347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033267763568484213078231 3049901645352726319617347)
                  ·
                    refine ⟨4574852468029089479426021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3049901645352726319617347 4574852468029089479426021)
                    ·
                      refine ⟨857784837755454277392379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4574852468029089479426021 857784837755454277392379)
                      ·
                        rfl

theorem cell23_1670530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_1670530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670530 prefixEnd_1670530 := by exact prefixLift 1670530
  have htrace : WordTrace (prefixWord ++ tailWord_1670530) baseStart_1670530 baseEnd_1670530 := by
    simpa [prefixWord, tailWord_1670530, baseEnd_1670530] using wordTrace_append hprefix tailTrace_1670530
  have hstable : (prefixWord ++ tailWord_1670530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670530).length < 2 ^ (prefixWord ++ tailWord_1670530).sum := by decide
  have hdescent : baseEnd_1670530 < baseStart_1670530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670545 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 3, 8]
def baseStart_1670545 : Nat := 118140960795 + 1670545 * 2 ^ 59
def prefixEnd_1670545 : Nat := 4983230072969 + 3 ^ 40 * 1670545 * 2
def baseEnd_1670545 : Nat := 285930846655090572901603

theorem tailTrace_1670545 : CollatzResearch.WordTrace tailWord_1670545 prefixEnd_1670545 285930846655090572901603 := by
  unfold tailWord_1670545
  simp only [CollatzResearch.WordTrace]
  refine ⟨60929781732908246216709089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40619854488605497477806059 60929781732908246216709089)
  ·
    refine ⟨45697336299681184662531817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60929781732908246216709089 45697336299681184662531817)
    ·
      refine ⟨34273002224760888496898863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45697336299681184662531817 34273002224760888496898863)
      ·
        refine ⟨51409503337141332745348295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34273002224760888496898863 51409503337141332745348295)
        ·
          refine ⟨77114255005711999118022443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51409503337141332745348295 77114255005711999118022443)
          ·
            refine ⟨115671382508567998677033665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77114255005711999118022443 115671382508567998677033665)
            ·
              refine ⟨86753536881425999007775249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115671382508567998677033665 86753536881425999007775249)
              ·
                refine ⟨65065152661069499255831437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86753536881425999007775249 65065152661069499255831437)
                ·
                  refine ⟨24399432247901062220936789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65065152661069499255831437 24399432247901062220936789)
                  ·
                    refine ⟨285930846655090572901603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24399432247901062220936789 285930846655090572901603)
                    ·
                      rfl

theorem cell23_1670545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_1670545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670545 prefixEnd_1670545 := by exact prefixLift 1670545
  have htrace : WordTrace (prefixWord ++ tailWord_1670545) baseStart_1670545 baseEnd_1670545 := by
    simpa [prefixWord, tailWord_1670545, baseEnd_1670545] using wordTrace_append hprefix tailTrace_1670545
  have hstable : (prefixWord ++ tailWord_1670545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670545).length < 2 ^ (prefixWord ++ tailWord_1670545).sum := by decide
  have hdescent : baseEnd_1670545 < baseStart_1670545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670572 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_1670572 : Nat := 118140960795 + 1670572 * 2 ^ 59
def prefixEnd_1670572 : Nat := 4983230072969 + 3 ^ 40 * 1670572 * 2
def baseEnd_1670572 : Nat := 857806403942943113067185

theorem tailTrace_1670572 : CollatzResearch.WordTrace tailWord_1670572 prefixEnd_1670572 857806403942943113067185 := by
  unfold tailWord_1670572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30465383251905214913970985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40620511002540286551961313 30465383251905214913970985)
  ·
    refine ⟨22849037438928911185478239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30465383251905214913970985 22849037438928911185478239)
    ·
      refine ⟨34273556158393366778217359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22849037438928911185478239 34273556158393366778217359)
      ·
        refine ⟨51410334237590050167326039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34273556158393366778217359 51410334237590050167326039)
        ·
          refine ⟨77115501356385075250989059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51410334237590050167326039 77115501356385075250989059)
          ·
            refine ⟨115673252034577612876483589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77115501356385075250989059 115673252034577612876483589)
            ·
              refine ⟨21688734756483302414340673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115673252034577612876483589 21688734756483302414340673)
              ·
                refine ⟨16266551067362476810755505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21688734756483302414340673 16266551067362476810755505)
                ·
                  refine ⟨12199913300521857608066629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16266551067362476810755505 12199913300521857608066629)
                  ·
                    refine ⟨2287483743847848301512493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12199913300521857608066629 2287483743847848301512493)
                    ·
                      refine ⟨857806403942943113067185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2287483743847848301512493 857806403942943113067185)
                      ·
                        rfl

theorem cell23_1670572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_1670572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670572 prefixEnd_1670572 := by exact prefixLift 1670572
  have htrace : WordTrace (prefixWord ++ tailWord_1670572) baseStart_1670572 baseEnd_1670572 := by
    simpa [prefixWord, tailWord_1670572, baseEnd_1670572] using wordTrace_append hprefix tailTrace_1670572
  have hstable : (prefixWord ++ tailWord_1670572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670572).length < 2 ^ (prefixWord ++ tailWord_1670572).sum := by decide
  have hdescent : baseEnd_1670572 < baseStart_1670572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670573 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_1670573 : Nat := 118140960795 + 1670573 * 2 ^ 59
def prefixEnd_1670573 : Nat := 4983230072969 + 3 ^ 40 * 1670573 * 2
def baseEnd_1670573 : Nat := 857806917423597609154681

theorem tailTrace_1670573 : CollatzResearch.WordTrace tailWord_1670573 prefixEnd_1670573 857806917423597609154681 := by
  unfold tailWord_1670573
  simp only [CollatzResearch.WordTrace]
  refine ⟨60930802976806806998728373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40620535317871204665818915 60930802976806806998728373)
  ·
    refine ⟨5712262779075638156130785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60930802976806806998728373 5712262779075638156130785)
    ·
      refine ⟨4284197084306728617098089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5712262779075638156130785 4284197084306728617098089)
      ·
        refine ⟨3213147813230046462823567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4284197084306728617098089 3213147813230046462823567)
        ·
          refine ⟨4819721719845069694235351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213147813230046462823567 4819721719845069694235351)
          ·
            refine ⟨7229582579767604541353027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4819721719845069694235351 7229582579767604541353027)
            ·
              refine ⟨10844373869651406812029541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7229582579767604541353027 10844373869651406812029541)
              ·
                refine ⟨2033320100559638777255539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10844373869651406812029541 2033320100559638777255539)
                ·
                  refine ⟨3049980150839458165883309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033320100559638777255539 3049980150839458165883309)
                  ·
                    refine ⟨1143742556564796812206241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3049980150839458165883309 1143742556564796812206241)
                    ·
                      refine ⟨857806917423597609154681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143742556564796812206241 857806917423597609154681)
                      ·
                        rfl

theorem cell23_1670573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_1670573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670573 prefixEnd_1670573 := by exact prefixLift 1670573
  have htrace : WordTrace (prefixWord ++ tailWord_1670573) baseStart_1670573 baseEnd_1670573 := by
    simpa [prefixWord, tailWord_1670573, baseEnd_1670573] using wordTrace_append hprefix tailTrace_1670573
  have hstable : (prefixWord ++ tailWord_1670573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670573).length < 2 ^ (prefixWord ++ tailWord_1670573).sum := by decide
  have hdescent : baseEnd_1670573 < baseStart_1670573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670632 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1670632 : Nat := 118140960795 + 1670632 * 2 ^ 59
def prefixEnd_1670632 : Nat := 4983230072969 + 3 ^ 40 * 1670632 * 2
def baseEnd_1670632 : Nat := 857837212782212878316909

theorem tailTrace_1670632 : CollatzResearch.WordTrace tailWord_1670632 prefixEnd_1670632 857837212782212878316909 := by
  unfold tailWord_1670632
  simp only [CollatzResearch.WordTrace]
  refine ⟨30466477441796530037563075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40621969922395373383417433 30466477441796530037563075)
  ·
    refine ⟨45699716162694795056344613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30466477441796530037563075 45699716162694795056344613)
    ·
      refine ⟨8568696780505274073064615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45699716162694795056344613 8568696780505274073064615)
      ·
        refine ⟨12853045170757911109596923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8568696780505274073064615 12853045170757911109596923)
        ·
          refine ⟨19279567756136866664395385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12853045170757911109596923 19279567756136866664395385)
          ·
            refine ⟨14459675817102649998296539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19279567756136866664395385 14459675817102649998296539)
            ·
              refine ⟨21689513725653974997444809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14459675817102649998296539 21689513725653974997444809)
              ·
                refine ⟨16267135294240481248083607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21689513725653974997444809 16267135294240481248083607)
                ·
                  refine ⟨24400702941360721872125411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16267135294240481248083607 24400702941360721872125411)
                  ·
                    refine ⟨36601054412041082808188117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24400702941360721872125411 36601054412041082808188117)
                    ·
                      refine ⟨857837212782212878316909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36601054412041082808188117 857837212782212878316909)
                      ·
                        rfl

theorem cell23_1670632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1670632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670632 prefixEnd_1670632 := by exact prefixLift 1670632
  have htrace : WordTrace (prefixWord ++ tailWord_1670632) baseStart_1670632 baseEnd_1670632 := by
    simpa [prefixWord, tailWord_1670632, baseEnd_1670632] using wordTrace_append hprefix tailTrace_1670632
  have hstable : (prefixWord ++ tailWord_1670632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670632).length < 2 ^ (prefixWord ++ tailWord_1670632).sum := by decide
  have hdescent : baseEnd_1670632 < baseStart_1670632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670660 : List Nat := [2, 3, 2, 3, 2, 2, 2, 2, 5]
def baseStart_1670660 : Nat := 118140960795 + 1670660 * 2 ^ 59
def prefixEnd_1670660 : Nat := 4983230072969 + 3 ^ 40 * 1670660 * 2
def baseEnd_1670660 : Nat := 95316843360059863196309

theorem tailTrace_1670660 : CollatzResearch.WordTrace tailWord_1670660 prefixEnd_1670660 95316843360059863196309 := by
  unfold tailWord_1670660
  simp only [CollatzResearch.WordTrace]
  refine ⟨30466988063745810428572717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40622650751661080571430289 30466988063745810428572717)
  ·
    refine ⟨11425120523904678910714769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30466988063745810428572717 11425120523904678910714769)
    ·
      refine ⟨8568840392928509183036077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11425120523904678910714769 8568840392928509183036077)
      ·
        refine ⟨3213315147348190943638529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8568840392928509183036077 3213315147348190943638529)
        ·
          refine ⟨2409986360511143207728897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3213315147348190943638529 2409986360511143207728897)
          ·
            refine ⟨1807489770383357405796673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2409986360511143207728897 1807489770383357405796673)
            ·
              refine ⟨1355617327787518054347505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807489770383357405796673 1355617327787518054347505)
              ·
                refine ⟨1016712995840638540760629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355617327787518054347505 1016712995840638540760629)
                ·
                  refine ⟨95316843360059863196309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016712995840638540760629 95316843360059863196309)
                  ·
                    rfl

theorem cell23_1670660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_1670660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670660 prefixEnd_1670660 := by exact prefixLift 1670660
  have htrace : WordTrace (prefixWord ++ tailWord_1670660) baseStart_1670660 baseEnd_1670660 := by
    simpa [prefixWord, tailWord_1670660, baseEnd_1670660] using wordTrace_append hprefix tailTrace_1670660
  have hstable : (prefixWord ++ tailWord_1670660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670660).length < 2 ^ (prefixWord ++ tailWord_1670660).sum := by decide
  have hdescent : baseEnd_1670660 < baseStart_1670660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670682 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 10]
def baseStart_1670682 : Nat := 118140960795 + 1670682 * 2 ^ 59
def prefixEnd_1670682 : Nat := 4983230072969 + 3 ^ 40 * 1670682 * 2
def baseEnd_1670682 : Nat := 95318098534993075854631

theorem tailTrace_1670682 : CollatzResearch.WordTrace tailWord_1670682 prefixEnd_1670682 95318098534993075854631 := by
  unfold tailWord_1670682
  simp only [CollatzResearch.WordTrace]
  refine ⟨15233694633352979653611575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40623185688941279076297533 15233694633352979653611575)
  ·
    refine ⟨22850541950029469480417363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15233694633352979653611575 22850541950029469480417363)
    ·
      refine ⟨34275812925044204220626045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22850541950029469480417363 34275812925044204220626045)
      ·
        refine ⟨12853429846891576582734767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34275812925044204220626045 12853429846891576582734767)
        ·
          refine ⟨19280144770337364874102151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12853429846891576582734767 19280144770337364874102151)
          ·
            refine ⟨28920217155506047311153227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19280144770337364874102151 28920217155506047311153227)
            ·
              refine ⟨43380325733259070966729841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28920217155506047311153227 43380325733259070966729841)
              ·
                refine ⟨32535244299944303225047381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43380325733259070966729841 32535244299944303225047381)
                ·
                  refine ⟨95318098534993075854631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 32535244299944303225047381 95318098534993075854631)
                  ·
                    rfl

theorem cell23_1670682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_1670682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670682 prefixEnd_1670682 := by exact prefixLift 1670682
  have htrace : WordTrace (prefixWord ++ tailWord_1670682) baseStart_1670682 baseEnd_1670682 := by
    simpa [prefixWord, tailWord_1670682, baseEnd_1670682] using wordTrace_append hprefix tailTrace_1670682
  have hstable : (prefixWord ++ tailWord_1670682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670682).length < 2 ^ (prefixWord ++ tailWord_1670682).sum := by decide
  have hdescent : baseEnd_1670682 < baseStart_1670682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670759 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 1, 6]
def baseStart_1670759 : Nat := 118140960795 + 1670759 * 2 ^ 59
def prefixEnd_1670759 : Nat := 4983230072969 + 3 ^ 40 * 1670759 * 2
def baseEnd_1670759 : Nat := 285967474941777960476275

theorem tailTrace_1670759 : CollatzResearch.WordTrace tailWord_1670759 prefixEnd_1670759 285967474941777960476275 := by
  unfold tailWord_1670759
  simp only [CollatzResearch.WordTrace]
  refine ⟨60937586954132960764999331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40625057969421973843332887 60937586954132960764999331)
  ·
    refine ⟨91406380431199441147498997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60937586954132960764999331 91406380431199441147498997)
    ·
      refine ⟨8569348165424947607578031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91406380431199441147498997 8569348165424947607578031)
      ·
        refine ⟨12854022248137421411367047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8569348165424947607578031 12854022248137421411367047)
        ·
          refine ⟨19281033372206132117050571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12854022248137421411367047 19281033372206132117050571)
          ·
            refine ⟨28921550058309198175575857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19281033372206132117050571 28921550058309198175575857)
            ·
              refine ⟨21691162543731898631681893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28921550058309198175575857 21691162543731898631681893)
              ·
                refine ⟨4067092976949730993440355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21691162543731898631681893 4067092976949730993440355)
                ·
                  refine ⟨6100639465424596490160533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067092976949730993440355 6100639465424596490160533)
                  ·
                    refine ⟨285967474941777960476275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6100639465424596490160533 285967474941777960476275)
                    ·
                      rfl

theorem cell23_1670759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_1670759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670759 prefixEnd_1670759 := by exact prefixLift 1670759
  have htrace : WordTrace (prefixWord ++ tailWord_1670759) baseStart_1670759 baseEnd_1670759 := by
    simpa [prefixWord, tailWord_1670759, baseEnd_1670759] using wordTrace_append hprefix tailTrace_1670759
  have hstable : (prefixWord ++ tailWord_1670759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670759).length < 2 ^ (prefixWord ++ tailWord_1670759).sum := by decide
  have hdescent : baseEnd_1670759 < baseStart_1670759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670789 : List Nat := [1, 3, 1, 1, 4, 1, 4, 8]
def baseStart_1670789 : Nat := 118140960795 + 1670789 * 2 ^ 59
def prefixEnd_1670789 : Nat := 4983230072969 + 3 ^ 40 * 1670789 * 2
def baseEnd_1670789 : Nat := 31774734416480324594581

theorem tailTrace_1670789 : CollatzResearch.WordTrace tailWord_1670789 prefixEnd_1670789 31774734416480324594581 := by
  unfold tailWord_1670789
  simp only [CollatzResearch.WordTrace]
  refine ⟨60938681144024275888591421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40625787429349517259060947 60938681144024275888591421)
  ·
    refine ⟨22852005429009103458221783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60938681144024275888591421 22852005429009103458221783)
    ·
      refine ⟨34278008143513655187332675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22852005429009103458221783 34278008143513655187332675)
      ·
        refine ⟨51417012215270482780999013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34278008143513655187332675 51417012215270482780999013)
        ·
          refine ⟨9640689790363215521437315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51417012215270482780999013 9640689790363215521437315)
          ·
            refine ⟨14461034685544823282155973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9640689790363215521437315 14461034685544823282155973)
            ·
              refine ⟨2711444003539654365404245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14461034685544823282155973 2711444003539654365404245)
              ·
                refine ⟨31774734416480324594581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2711444003539654365404245 31774734416480324594581)
                ·
                  rfl

theorem cell23_1670789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 8].length) (baseStart_1670789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670789 prefixEnd_1670789 := by exact prefixLift 1670789
  have htrace : WordTrace (prefixWord ++ tailWord_1670789) baseStart_1670789 baseEnd_1670789 := by
    simpa [prefixWord, tailWord_1670789, baseEnd_1670789] using wordTrace_append hprefix tailTrace_1670789
  have hstable : (prefixWord ++ tailWord_1670789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670789).length < 2 ^ (prefixWord ++ tailWord_1670789).sum := by decide
  have hdescent : baseEnd_1670789 < baseStart_1670789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670793 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 2, 4]
def baseStart_1670793 : Nat := 118140960795 + 1670793 * 2 ^ 59
def prefixEnd_1670793 : Nat := 4983230072969 + 3 ^ 40 * 1670793 * 2
def baseEnd_1670793 : Nat := 285973294389195582801223

theorem tailTrace_1670793 : CollatzResearch.WordTrace tailWord_1670793 prefixEnd_1670793 285973294389195582801223 := by
  unfold tailWord_1670793
  simp only [CollatzResearch.WordTrace]
  refine ⟨60938827036009784571737033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40625884690673189714491355 60938827036009784571737033)
  ·
    refine ⟨45704120277007338428802775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60938827036009784571737033 45704120277007338428802775)
    ·
      refine ⟨68556180415511007643204163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45704120277007338428802775 68556180415511007643204163)
      ·
        refine ⟨102834270623266511464806245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68556180415511007643204163 102834270623266511464806245)
        ·
          refine ⟨19281425741862470899651171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102834270623266511464806245 19281425741862470899651171)
          ·
            refine ⟨28922138612793706349476757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19281425741862470899651171 28922138612793706349476757)
            ·
              refine ⟨1355725247474704985131723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28922138612793706349476757 1355725247474704985131723)
              ·
                refine ⟨2033587871212057477697585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355725247474704985131723 2033587871212057477697585)
                ·
                  refine ⟨1525190903409043108273189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2033587871212057477697585 1525190903409043108273189)
                  ·
                    refine ⟨285973294389195582801223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1525190903409043108273189 285973294389195582801223)
                    ·
                      rfl

theorem cell23_1670793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 4].length) (baseStart_1670793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670793 prefixEnd_1670793 := by exact prefixLift 1670793
  have htrace : WordTrace (prefixWord ++ tailWord_1670793) baseStart_1670793 baseEnd_1670793 := by
    simpa [prefixWord, tailWord_1670793, baseEnd_1670793] using wordTrace_append hprefix tailTrace_1670793
  have hstable : (prefixWord ++ tailWord_1670793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670793).length < 2 ^ (prefixWord ++ tailWord_1670793).sum := by decide
  have hdescent : baseEnd_1670793 < baseStart_1670793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670816 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1670816 : Nat := 118140960795 + 1670816 * 2 ^ 59
def prefixEnd_1670816 : Nat := 4983230072969 + 3 ^ 40 * 1670816 * 2
def baseEnd_1670816 : Nat := 857931693222640158416063

theorem tailTrace_1670816 : CollatzResearch.WordTrace tailWord_1670816 prefixEnd_1670816 857931693222640158416063 := by
  unfold tailWord_1670816
  simp only [CollatzResearch.WordTrace]
  refine ⟨30469832957463229749912151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40626443943284306333216201 30469832957463229749912151)
  ·
    refine ⟨45704749436194844624868227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30469832957463229749912151 45704749436194844624868227)
    ·
      refine ⟨68557124154292266937302341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45704749436194844624868227 68557124154292266937302341)
      ·
        refine ⟨12854460778929800050744189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68557124154292266937302341 12854460778929800050744189)
        ·
          refine ⟨4820422792098675019029071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12854460778929800050744189 4820422792098675019029071)
          ·
            refine ⟨7230634188148012528543607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820422792098675019029071 7230634188148012528543607)
            ·
              refine ⟨10845951282222018792815411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7230634188148012528543607 10845951282222018792815411)
              ·
                refine ⟨16268926923333028189223117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10845951282222018792815411 16268926923333028189223117)
                ·
                  refine ⟨6100847596249885570958669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16268926923333028189223117 6100847596249885570958669)
                  ·
                    refine ⟨2287817848593707089109501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6100847596249885570958669 2287817848593707089109501)
                    ·
                      refine ⟨857931693222640158416063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2287817848593707089109501 857931693222640158416063)
                      ·
                        rfl

theorem cell23_1670816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1670816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670816 prefixEnd_1670816 := by exact prefixLift 1670816
  have htrace : WordTrace (prefixWord ++ tailWord_1670816) baseStart_1670816 baseEnd_1670816 := by
    simpa [prefixWord, tailWord_1670816, baseEnd_1670816] using wordTrace_append hprefix tailTrace_1670816
  have hstable : (prefixWord ++ tailWord_1670816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670816).length < 2 ^ (prefixWord ++ tailWord_1670816).sum := by decide
  have hdescent : baseEnd_1670816 < baseStart_1670816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670820 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_1670820 : Nat := 118140960795 + 1670820 * 2 ^ 59
def prefixEnd_1670820 : Nat := 4983230072969 + 3 ^ 40 * 1670820 * 2
def baseEnd_1670820 : Nat := 857933747145258142766045

theorem tailTrace_1670820 : CollatzResearch.WordTrace tailWord_1670820 prefixEnd_1670820 857933747145258142766045 := by
  unfold tailWord_1670820
  simp only [CollatzResearch.WordTrace]
  refine ⟨30469905903455984091484957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40626541204607978788646609 30469905903455984091484957)
  ·
    refine ⟨11426214713795994034306859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30469905903455984091484957 11426214713795994034306859)
    ·
      refine ⟨17139322070693991051460289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11426214713795994034306859 17139322070693991051460289)
      ·
        refine ⟨12854491553020493288595217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17139322070693991051460289 12854491553020493288595217)
        ·
          refine ⟨9640868664765369966446413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12854491553020493288595217 9640868664765369966446413)
          ·
            refine ⟨3615325749287013737417405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9640868664765369966446413 3615325749287013737417405)
            ·
              refine ⟨1355747155982630151531527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3615325749287013737417405 1355747155982630151531527)
              ·
                refine ⟨2033620733973945227297291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355747155982630151531527 2033620733973945227297291)
                ·
                  refine ⟨3050431100960917840945937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033620733973945227297291 3050431100960917840945937)
                  ·
                    refine ⟨2287823325720688380709453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3050431100960917840945937 2287823325720688380709453)
                    ·
                      refine ⟨857933747145258142766045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2287823325720688380709453 857933747145258142766045)
                      ·
                        rfl

theorem cell23_1670820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_1670820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670820 prefixEnd_1670820 := by exact prefixLift 1670820
  have htrace : WordTrace (prefixWord ++ tailWord_1670820) baseStart_1670820 baseEnd_1670820 := by
    simpa [prefixWord, tailWord_1670820, baseEnd_1670820] using wordTrace_append hprefix tailTrace_1670820
  have hstable : (prefixWord ++ tailWord_1670820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670820).length < 2 ^ (prefixWord ++ tailWord_1670820).sum := by decide
  have hdescent : baseEnd_1670820 < baseStart_1670820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670859 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 5]
def baseStart_1670859 : Nat := 118140960795 + 1670859 * 2 ^ 59
def prefixEnd_1670859 : Nat := 4983230072969 + 3 ^ 40 * 1670859 * 2
def baseEnd_1670859 : Nat := 857953772890783490178365

theorem tailTrace_1670859 : CollatzResearch.WordTrace tailWord_1670859 prefixEnd_1670859 857953772890783490178365 := by
  unfold tailWord_1670859
  simp only [CollatzResearch.WordTrace]
  refine ⟨60941234253770677843639631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40627489502513785229093087 60941234253770677843639631)
  ·
    refine ⟨91411851380656016765459447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60941234253770677843639631 91411851380656016765459447)
    ·
      refine ⟨137117777070984025148189171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91411851380656016765459447 137117777070984025148189171)
      ·
        refine ⟨205676665606476037722283757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137117777070984025148189171 205676665606476037722283757)
        ·
          refine ⟨77128749602428514145856409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205676665606476037722283757 77128749602428514145856409)
          ·
            refine ⟨57846562201821385609392307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77128749602428514145856409 57846562201821385609392307)
            ·
              refine ⟨86769843302732078414088461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57846562201821385609392307 86769843302732078414088461)
              ·
                refine ⟨32538691238524529405283173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86769843302732078414088461 32538691238524529405283173)
                ·
                  refine ⟨6101004607223349263490595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32538691238524529405283173 6101004607223349263490595)
                  ·
                    refine ⟨9151506910835023895235893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6101004607223349263490595 9151506910835023895235893)
                    ·
                      refine ⟨857953772890783490178365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9151506910835023895235893 857953772890783490178365)
                      ·
                        rfl

theorem cell23_1670859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 5].length) (baseStart_1670859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670859 prefixEnd_1670859 := by exact prefixLift 1670859
  have htrace : WordTrace (prefixWord ++ tailWord_1670859) baseStart_1670859 baseEnd_1670859 := by
    simpa [prefixWord, tailWord_1670859, baseEnd_1670859] using wordTrace_append hprefix tailTrace_1670859
  have hstable : (prefixWord ++ tailWord_1670859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670859).length < 2 ^ (prefixWord ++ tailWord_1670859).sum := by decide
  have hdescent : baseEnd_1670859 < baseStart_1670859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670873 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 1, 4, 2]
def baseStart_1670873 : Nat := 118140960795 + 1670873 * 2 ^ 59
def prefixEnd_1670873 : Nat := 4983230072969 + 3 ^ 40 * 1670873 * 2
def baseEnd_1670873 : Nat := 857960961619946435403301

theorem tailTrace_1670873 : CollatzResearch.WordTrace tailWord_1670873 prefixEnd_1670873 857960961619946435403301 := by
  unfold tailWord_1670873
  simp only [CollatzResearch.WordTrace]
  refine ⟨60941744875719958234649273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40627829917146638823099515 60941744875719958234649273)
  ·
    refine ⟨45706308656789968675986955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60941744875719958234649273 45706308656789968675986955)
    ·
      refine ⟨68559462985184953013980433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45706308656789968675986955 68559462985184953013980433)
      ·
        refine ⟨51419597238888714760485325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68559462985184953013980433 51419597238888714760485325)
        ·
          refine ⟨19282348964583268035181997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51419597238888714760485325 19282348964583268035181997)
          ·
            refine ⟨7230880861718725513193249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19282348964583268035181997 7230880861718725513193249)
            ·
              refine ⟨5423160646289044134894937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7230880861718725513193249 5423160646289044134894937)
              ·
                refine ⟨4067370484716783101171203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5423160646289044134894937 4067370484716783101171203)
                ·
                  refine ⟨6101055727075174651756805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067370484716783101171203 6101055727075174651756805)
                  ·
                    refine ⟨1143947948826595247204401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6101055727075174651756805 1143947948826595247204401)
                    ·
                      refine ⟨857960961619946435403301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1143947948826595247204401 857960961619946435403301)
                      ·
                        rfl

theorem cell23_1670873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_1670873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670873 prefixEnd_1670873 := by exact prefixLift 1670873
  have htrace : WordTrace (prefixWord ++ tailWord_1670873) baseStart_1670873 baseEnd_1670873 := by
    simpa [prefixWord, tailWord_1670873, baseEnd_1670873] using wordTrace_append hprefix tailTrace_1670873
  have hstable : (prefixWord ++ tailWord_1670873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670873).length < 2 ^ (prefixWord ++ tailWord_1670873).sum := by decide
  have hdescent : baseEnd_1670873 < baseStart_1670873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670879 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 9]
def baseStart_1670879 : Nat := 118140960795 + 1670879 * 2 ^ 59
def prefixEnd_1670879 : Nat := 4983230072969 + 3 ^ 40 * 1670879 * 2
def baseEnd_1670879 : Nat := 95329338055985934658697

theorem tailTrace_1670879 : CollatzResearch.WordTrace tailWord_1670879 prefixEnd_1670879 95329338055985934658697 := by
  unfold tailWord_1670879
  simp only [CollatzResearch.WordTrace]
  refine ⟨60941963713698221259367691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40627975809132147506245127 60941963713698221259367691)
  ·
    refine ⟨91412945570547331889051537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60941963713698221259367691 91412945570547331889051537)
    ·
      refine ⟨68559709177910498916788653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91412945570547331889051537 68559709177910498916788653)
      ·
        refine ⟨25709890941716437093795745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68559709177910498916788653 25709890941716437093795745)
        ·
          refine ⟨19282418206287327820346809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25709890941716437093795745 19282418206287327820346809)
          ·
            refine ⟨14461813654715495865260107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19282418206287327820346809 14461813654715495865260107)
            ·
              refine ⟨21692720482073243797890161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14461813654715495865260107 21692720482073243797890161)
              ·
                refine ⟨16269540361554932848417621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21692720482073243797890161 16269540361554932848417621)
                ·
                  refine ⟨95329338055985934658697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16269540361554932848417621 95329338055985934658697)
                  ·
                    rfl

theorem cell23_1670879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 9].length) (baseStart_1670879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670879 prefixEnd_1670879 := by exact prefixLift 1670879
  have htrace : WordTrace (prefixWord ++ tailWord_1670879) baseStart_1670879 baseEnd_1670879 := by
    simpa [prefixWord, tailWord_1670879, baseEnd_1670879] using wordTrace_append hprefix tailTrace_1670879
  have hstable : (prefixWord ++ tailWord_1670879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670879).length < 2 ^ (prefixWord ++ tailWord_1670879).sum := by decide
  have hdescent : baseEnd_1670879 < baseStart_1670879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670900 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1670900 : Nat := 118140960795 + 1670900 * 2 ^ 59
def prefixEnd_1670900 : Nat := 4983230072969 + 3 ^ 40 * 1670900 * 2
def baseEnd_1670900 : Nat := 285991608532539276588559

theorem tailTrace_1670900 : CollatzResearch.WordTrace tailWord_1670900 prefixEnd_1670900 285991608532539276588559 := by
  unfold tailWord_1670900
  simp only [CollatzResearch.WordTrace]
  refine ⟨30471364823311070922941077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40628486431081427897254769 30471364823311070922941077)
  ·
    refine ⟨1428345226092706449512863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30471364823311070922941077 1428345226092706449512863)
    ·
      refine ⟨2142517839139059674269295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428345226092706449512863 2142517839139059674269295)
      ·
        refine ⟨3213776758708589511403943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142517839139059674269295 3213776758708589511403943)
        ·
          refine ⟨4820665138062884267105915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213776758708589511403943 4820665138062884267105915)
          ·
            refine ⟨7230997707094326400658873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820665138062884267105915 7230997707094326400658873)
            ·
              refine ⟨5423248280320744800494155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7230997707094326400658873 5423248280320744800494155)
              ·
                refine ⟨8134872420481117200741233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423248280320744800494155 8134872420481117200741233)
                ·
                  refine ⟨6101154315360837900555925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134872420481117200741233 6101154315360837900555925)
                  ·
                    refine ⟨285991608532539276588559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6101154315360837900555925 285991608532539276588559)
                    ·
                      rfl

theorem cell23_1670900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1670900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670900 prefixEnd_1670900 := by exact prefixLift 1670900
  have htrace : WordTrace (prefixWord ++ tailWord_1670900) baseStart_1670900 baseEnd_1670900 := by
    simpa [prefixWord, tailWord_1670900, baseEnd_1670900] using wordTrace_append hprefix tailTrace_1670900
  have hstable : (prefixWord ++ tailWord_1670900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670900).length < 2 ^ (prefixWord ++ tailWord_1670900).sum := by decide
  have hdescent : baseEnd_1670900 < baseStart_1670900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670926 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_1670926 : Nat := 118140960795 + 1670926 * 2 ^ 59
def prefixEnd_1670926 : Nat := 4983230072969 + 3 ^ 40 * 1670926 * 2
def baseEnd_1670926 : Nat := 285996058698211576013519

theorem tailTrace_1670926 : CollatzResearch.WordTrace tailWord_1670926 prefixEnd_1670926 285996058698211576013519 := by
  unfold tailWord_1670926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7617959743065993535791079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40629118629685298857552421 7617959743065993535791079)
  ·
    refine ⟨11426939614598990303686619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7617959743065993535791079 11426939614598990303686619)
    ·
      refine ⟨17140409421898485455529929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11426939614598990303686619 17140409421898485455529929)
      ·
        refine ⟨12855307066423864091647447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17140409421898485455529929 12855307066423864091647447)
        ·
          refine ⟨19282960599635796137471171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12855307066423864091647447 19282960599635796137471171)
          ·
            refine ⟨28924440899453694206206757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19282960599635796137471171 28924440899453694206206757)
            ·
              refine ⟨5423332668647567663663767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28924440899453694206206757 5423332668647567663663767)
              ·
                refine ⟨8134999002971351495495651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423332668647567663663767 8134999002971351495495651)
                ·
                  refine ⟨12202498504457027243243477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8134999002971351495495651 12202498504457027243243477)
                  ·
                    refine ⟨285996058698211576013519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12202498504457027243243477 285996058698211576013519)
                    ·
                      rfl

theorem cell23_1670926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_1670926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670926 prefixEnd_1670926 := by exact prefixLift 1670926
  have htrace : WordTrace (prefixWord ++ tailWord_1670926) baseStart_1670926 baseEnd_1670926 := by
    simpa [prefixWord, tailWord_1670926, baseEnd_1670926] using wordTrace_append hprefix tailTrace_1670926
  have hstable : (prefixWord ++ tailWord_1670926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670926).length < 2 ^ (prefixWord ++ tailWord_1670926).sum := by decide
  have hdescent : baseEnd_1670926 < baseStart_1670926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670939 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 1, 10]
def baseStart_1670939 : Nat := 118140960795 + 1670939 * 2 ^ 59
def prefixEnd_1670939 : Nat := 4983230072969 + 3 ^ 40 * 1670939 * 2
def baseEnd_1670939 : Nat := 285998283781047725725999

theorem tailTrace_1670939 : CollatzResearch.WordTrace tailWord_1670939 prefixEnd_1670939 285998283781047725725999 := by
  unfold tailWord_1670939
  simp only [CollatzResearch.WordTrace]
  refine ⟨60944152093480851506551871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40629434728987234337701247 60944152093480851506551871)
  ·
    refine ⟨91416228140221277259827807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60944152093480851506551871 91416228140221277259827807)
    ·
      refine ⟨137124342210331915889741711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91416228140221277259827807 137124342210331915889741711)
      ·
        refine ⟨205686513315497873834612567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137124342210331915889741711 205686513315497873834612567)
        ·
          refine ⟨308529769973246810751918851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205686513315497873834612567 308529769973246810751918851)
          ·
            refine ⟨462794654959870216127878277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308529769973246810751918851 462794654959870216127878277)
            ·
              refine ⟨86773997804975665523977177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 462794654959870216127878277 86773997804975665523977177)
              ·
                refine ⟨65080498353731749142982883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86773997804975665523977177 65080498353731749142982883)
                ·
                  refine ⟨97620747530597623714474325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65080498353731749142982883 97620747530597623714474325)
                  ·
                    refine ⟨285998283781047725725999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 97620747530597623714474325 285998283781047725725999)
                    ·
                      rfl

theorem cell23_1670939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 10].length) (baseStart_1670939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670939 prefixEnd_1670939 := by exact prefixLift 1670939
  have htrace : WordTrace (prefixWord ++ tailWord_1670939) baseStart_1670939 baseEnd_1670939 := by
    simpa [prefixWord, tailWord_1670939, baseEnd_1670939] using wordTrace_append hprefix tailTrace_1670939
  have hstable : (prefixWord ++ tailWord_1670939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670939).length < 2 ^ (prefixWord ++ tailWord_1670939).sum := by decide
  have hdescent : baseEnd_1670939 < baseStart_1670939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670958 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1670958 : Nat := 118140960795 + 1670958 * 2 ^ 59
def prefixEnd_1670958 : Nat := 4983230072969 + 3 ^ 40 * 1670958 * 2
def baseEnd_1670958 : Nat := 858004607475578602840411

theorem tailTrace_1670958 : CollatzResearch.WordTrace tailWord_1670958 prefixEnd_1670958 858004607475578602840411 := by
  unfold tailWord_1670958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7618105635051502218936691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40629896720274678500995685 7618105635051502218936691)
  ·
    refine ⟨11427158452577253328405037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7618105635051502218936691 11427158452577253328405037)
    ·
      refine ⟨4285184419716469998151889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11427158452577253328405037 4285184419716469998151889)
      ·
        refine ⟨3213888314787352498613917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4285184419716469998151889 3213888314787352498613917)
        ·
          refine ⟨1205208118045257186980219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3213888314787352498613917 1205208118045257186980219)
          ·
            refine ⟨1807812177067885780470329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205208118045257186980219 1807812177067885780470329)
            ·
              refine ⟨1355859132800914335352747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807812177067885780470329 1355859132800914335352747)
              ·
                refine ⟨2033788699201371503029121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355859132800914335352747 2033788699201371503029121)
                ·
                  refine ⟨1525341524401028627271841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2033788699201371503029121 1525341524401028627271841)
                  ·
                    refine ⟨1144006143300771470453881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1525341524401028627271841 1144006143300771470453881)
                    ·
                      refine ⟨858004607475578602840411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144006143300771470453881 858004607475578602840411)
                      ·
                        rfl

theorem cell23_1670958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1670958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670958 prefixEnd_1670958 := by exact prefixLift 1670958
  have htrace : WordTrace (prefixWord ++ tailWord_1670958) baseStart_1670958 baseEnd_1670958 := by
    simpa [prefixWord, tailWord_1670958, baseEnd_1670958] using wordTrace_append hprefix tailTrace_1670958
  have hstable : (prefixWord ++ tailWord_1670958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670958).length < 2 ^ (prefixWord ++ tailWord_1670958).sum := by decide
  have hdescent : baseEnd_1670958 < baseStart_1670958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670983 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_1670983 : Nat := 118140960795 + 1670983 * 2 ^ 59
def prefixEnd_1670983 : Nat := 4983230072969 + 3 ^ 40 * 1670983 * 2
def baseEnd_1670983 : Nat := 858017444491941005027795

theorem tailTrace_1670983 : CollatzResearch.WordTrace tailWord_1670983 prefixEnd_1670983 858017444491941005027795 := by
  unfold tailWord_1670983
  simp only [CollatzResearch.WordTrace]
  refine ⟨60945756905321447021153603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40630504603547631347435735 60945756905321447021153603)
  ·
    refine ⟨91418635357982170531730405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60945756905321447021153603 91418635357982170531730405)
    ·
      refine ⟨17140994129621656974699451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91418635357982170531730405 17140994129621656974699451)
      ·
        refine ⟨25711491194432485462049177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17140994129621656974699451 25711491194432485462049177)
        ·
          refine ⟨19283618395824364096536883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25711491194432485462049177 19283618395824364096536883)
          ·
            refine ⟨28925427593736546144805325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19283618395824364096536883 28925427593736546144805325)
            ·
              refine ⟨10847035347651204804301997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28925427593736546144805325 10847035347651204804301997)
              ·
                refine ⟨4067638255369201801613249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10847035347651204804301997 4067638255369201801613249)
                ·
                  refine ⟨3050728691526901351209937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4067638255369201801613249 3050728691526901351209937)
                  ·
                    refine ⟨2288046518645176013407453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3050728691526901351209937 2288046518645176013407453)
                    ·
                      refine ⟨858017444491941005027795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2288046518645176013407453 858017444491941005027795)
                      ·
                        rfl

theorem cell23_1670983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_1670983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1670983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1670983 prefixEnd_1670983 := by exact prefixLift 1670983
  have htrace : WordTrace (prefixWord ++ tailWord_1670983) baseStart_1670983 baseEnd_1670983 := by
    simpa [prefixWord, tailWord_1670983, baseEnd_1670983] using wordTrace_append hprefix tailTrace_1670983
  have hstable : (prefixWord ++ tailWord_1670983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670983).length < 2 ^ (prefixWord ++ tailWord_1670983).sum := by decide
  have hdescent : baseEnd_1670983 < baseStart_1670983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671007 : List Nat := [1, 1, 2, 3, 1, 4, 4, 2, 1, 4]
def baseStart_1671007 : Nat := 118140960795 + 1671007 * 2 ^ 59
def prefixEnd_1671007 : Nat := 4983230072969 + 3 ^ 40 * 1671007 * 2
def baseEnd_1671007 : Nat := 286009922675882970375895

theorem tailTrace_1671007 : CollatzResearch.WordTrace tailWord_1671007 prefixEnd_1671007 286009922675882970375895 := by
  unfold tailWord_1671007
  simp only [CollatzResearch.WordTrace]
  refine ⟨60946632257234499120027275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40631088171489666080018183 60946632257234499120027275)
  ·
    refine ⟨91419948385851748680040913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60946632257234499120027275 91419948385851748680040913)
    ·
      refine ⟨68564961289388811510030685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91419948385851748680040913 68564961289388811510030685)
      ·
        refine ⟨25711860483520804316261507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68564961289388811510030685 25711860483520804316261507)
        ·
          refine ⟨38567790725281206474392261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25711860483520804316261507 38567790725281206474392261)
          ·
            refine ⟨7231460760990226213948549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38567790725281206474392261 7231460760990226213948549)
            ·
              refine ⟨1355898892685667415115353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7231460760990226213948549 1355898892685667415115353)
              ·
                refine ⟨1016924169514250561336515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355898892685667415115353 1016924169514250561336515)
                ·
                  refine ⟨1525386254271375842004773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016924169514250561336515 1525386254271375842004773)
                  ·
                    refine ⟨286009922675882970375895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1525386254271375842004773 286009922675882970375895)
                    ·
                      rfl

theorem cell23_1671007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 4].length) (baseStart_1671007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671007 prefixEnd_1671007 := by exact prefixLift 1671007
  have htrace : WordTrace (prefixWord ++ tailWord_1671007) baseStart_1671007 baseEnd_1671007 := by
    simpa [prefixWord, tailWord_1671007, baseEnd_1671007] using wordTrace_append hprefix tailTrace_1671007
  have hstable : (prefixWord ++ tailWord_1671007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671007).length < 2 ^ (prefixWord ++ tailWord_1671007).sum := by decide
  have hdescent : baseEnd_1671007 < baseStart_1671007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671026 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1671026 : Nat := 118140960795 + 1671026 * 2 ^ 59
def prefixEnd_1671026 : Nat := 4983230072969 + 3 ^ 40 * 1671026 * 2
def baseEnd_1671026 : Nat := 858039524160084336790097

theorem tailTrace_1671026 : CollatzResearch.WordTrace tailWord_1671026 prefixEnd_1671026 858039524160084336790097 := by
  unfold tailWord_1671026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15236831311041416341242233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40631550162777110243312621 15236831311041416341242233)
  ·
    refine ⟨11427623483281062255931675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15236831311041416341242233 11427623483281062255931675)
    ·
      refine ⟨17141435224921593383897513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11427623483281062255931675 17141435224921593383897513)
      ·
        refine ⟨12856076418691195037923135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17141435224921593383897513 12856076418691195037923135)
        ·
          refine ⟨19284114628036792556884703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12856076418691195037923135 19284114628036792556884703)
          ·
            refine ⟨28926171942055188835327055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284114628036792556884703 28926171942055188835327055)
            ·
              refine ⟨43389257913082783252990583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28926171942055188835327055 43389257913082783252990583)
              ·
                refine ⟨65083886869624174879485875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43389257913082783252990583 65083886869624174879485875)
                ·
                  refine ⟨97625830304436262319228813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65083886869624174879485875 97625830304436262319228813)
                  ·
                    refine ⟨36609686364163598369710805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97625830304436262319228813 36609686364163598369710805)
                    ·
                      refine ⟨858039524160084336790097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36609686364163598369710805 858039524160084336790097)
                      ·
                        rfl

theorem cell23_1671026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1671026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671026 prefixEnd_1671026 := by exact prefixLift 1671026
  have htrace : WordTrace (prefixWord ++ tailWord_1671026) baseStart_1671026 baseEnd_1671026 := by
    simpa [prefixWord, tailWord_1671026, baseEnd_1671026] using wordTrace_append hprefix tailTrace_1671026
  have hstable : (prefixWord ++ tailWord_1671026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671026).length < 2 ^ (prefixWord ++ tailWord_1671026).sum := by decide
  have hdescent : baseEnd_1671026 < baseStart_1671026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671033 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 1, 5]
def baseStart_1671033 : Nat := 118140960795 + 1671033 * 2 ^ 59
def prefixEnd_1671033 : Nat := 4983230072969 + 3 ^ 40 * 1671033 * 2
def baseEnd_1671033 : Nat := 286014372841555269800855

theorem tailTrace_1671033 : CollatzResearch.WordTrace tailWord_1671033 prefixEnd_1671033 286014372841555269800855 := by
  unfold tailWord_1671033
  simp only [CollatzResearch.WordTrace]
  refine ⟨60947580555140305560473753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40631720370093537040315835 60947580555140305560473753)
  ·
    refine ⟨45710685416355229170355315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60947580555140305560473753 45710685416355229170355315)
    ·
      refine ⟨68566028124532843755532973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45710685416355229170355315 68566028124532843755532973)
      ·
        refine ⟨25712260546699816408324865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68566028124532843755532973 25712260546699816408324865)
        ·
          refine ⟨19284195410024862306243649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25712260546699816408324865 19284195410024862306243649)
          ·
            refine ⟨14463146557518646729682737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19284195410024862306243649 14463146557518646729682737)
            ·
              refine ⟨10847359918138985047262053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14463146557518646729682737 10847359918138985047262053)
              ·
                refine ⟨2033879984651059696361635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10847359918138985047262053 2033879984651059696361635)
                ·
                  refine ⟨3050819976976589544542453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033879984651059696361635 3050819976976589544542453)
                  ·
                    refine ⟨286014372841555269800855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3050819976976589544542453 286014372841555269800855)
                    ·
                      rfl

theorem cell23_1671033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 5].length) (baseStart_1671033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671033 prefixEnd_1671033 := by exact prefixLift 1671033
  have htrace : WordTrace (prefixWord ++ tailWord_1671033) baseStart_1671033 baseEnd_1671033 := by
    simpa [prefixWord, tailWord_1671033, baseEnd_1671033] using wordTrace_append hprefix tailTrace_1671033
  have hstable : (prefixWord ++ tailWord_1671033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671033).length < 2 ^ (prefixWord ++ tailWord_1671033).sum := by decide
  have hdescent : baseEnd_1671033 < baseStart_1671033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671054 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_1671054 : Nat := 118140960795 + 1671054 * 2 ^ 59
def prefixEnd_1671054 : Nat := 4983230072969 + 3 ^ 40 * 1671054 * 2
def baseEnd_1671054 : Nat := 95339322402045580804441

theorem tailTrace_1671054 : CollatzResearch.WordTrace tailWord_1671054 prefixEnd_1671054 95339322402045580804441 := by
  unfold tailWord_1671054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7618543311008028268373527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40632230992042817431325477 7618543311008028268373527)
  ·
    refine ⟨11427814966512042402560291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7618543311008028268373527 11427814966512042402560291)
    ·
      refine ⟨17141722449768063603840437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11427814966512042402560291 17141722449768063603840437)
      ·
        refine ⟨1607036479665755962860041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17141722449768063603840437 1607036479665755962860041)
        ·
          refine ⟨1205277359749316972145031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1607036479665755962860041 1205277359749316972145031)
          ·
            refine ⟨1807916039623975458217547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205277359749316972145031 1807916039623975458217547)
            ·
              refine ⟨2711874059435963187326321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807916039623975458217547 2711874059435963187326321)
              ·
                refine ⟨2033905544576972390494741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711874059435963187326321 2033905544576972390494741)
                ·
                  refine ⟨95339322402045580804441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2033905544576972390494741 95339322402045580804441)
                  ·
                    rfl

theorem cell23_1671054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_1671054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671054 prefixEnd_1671054 := by exact prefixLift 1671054
  have htrace : WordTrace (prefixWord ++ tailWord_1671054) baseStart_1671054 baseEnd_1671054 := by
    simpa [prefixWord, tailWord_1671054, baseEnd_1671054] using wordTrace_append hprefix tailTrace_1671054
  have hstable : (prefixWord ++ tailWord_1671054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671054).length < 2 ^ (prefixWord ++ tailWord_1671054).sum := by decide
  have hdescent : baseEnd_1671054 < baseStart_1671054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671064 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1671064 : Nat := 118140960795 + 1671064 * 2 ^ 59
def prefixEnd_1671064 : Nat := 4983230072969 + 3 ^ 40 * 1671064 * 2
def baseEnd_1671064 : Nat := 858059036424955188114923

theorem tailTrace_1671064 : CollatzResearch.WordTrace tailWord_1671064 prefixEnd_1671064 858059036424955188114923 := by
  unfold tailWord_1671064
  simp only [CollatzResearch.WordTrace]
  refine ⟨30474355609013998927426123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40632474145351998569901497 30474355609013998927426123)
  ·
    refine ⟨45711533413520998391139185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30474355609013998927426123 45711533413520998391139185)
    ·
      refine ⟨34283650060140748793354389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45711533413520998391139185 34283650060140748793354389)
      ·
        refine ⟨1607046096569097599688487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34283650060140748793354389 1607046096569097599688487)
        ·
          refine ⟨2410569144853646399532731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607046096569097599688487 2410569144853646399532731)
          ·
            refine ⟨3615853717280469599299097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2410569144853646399532731 3615853717280469599299097)
            ·
              refine ⟨2711890287960352199474323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3615853717280469599299097 2711890287960352199474323)
              ·
                refine ⟨4067835431940528299211485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711890287960352199474323 4067835431940528299211485)
                ·
                  refine ⟨1525438286977698112204307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4067835431940528299211485 1525438286977698112204307)
                  ·
                    refine ⟨2288157430466547168306461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1525438286977698112204307 2288157430466547168306461)
                    ·
                      refine ⟨858059036424955188114923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2288157430466547168306461 858059036424955188114923)
                      ·
                        rfl

theorem cell23_1671064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1671064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671064 prefixEnd_1671064 := by exact prefixLift 1671064
  have htrace : WordTrace (prefixWord ++ tailWord_1671064) baseStart_1671064 baseEnd_1671064 := by
    simpa [prefixWord, tailWord_1671064, baseEnd_1671064] using wordTrace_append hprefix tailTrace_1671064
  have hstable : (prefixWord ++ tailWord_1671064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671064).length < 2 ^ (prefixWord ++ tailWord_1671064).sum := by decide
  have hdescent : baseEnd_1671064 < baseStart_1671064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671093 : List Nat := [1, 3, 3, 2, 1, 3, 1, 9]
def baseStart_1671093 : Nat := 118140960795 + 1671093 * 2 ^ 59
def prefixEnd_1671093 : Nat := 4983230072969 + 3 ^ 40 * 1671093 * 2
def baseEnd_1671093 : Nat := 31780515828293910172307

theorem tailTrace_1671093 : CollatzResearch.WordTrace tailWord_1671093 prefixEnd_1671093 31780515828293910172307 := by
  unfold tailWord_1671093
  simp only [CollatzResearch.WordTrace]
  refine ⟨60949768934922935807657933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40633179289948623871771955 60949768934922935807657933)
  ·
    refine ⟨22856163350596100927871725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60949768934922935807657933 22856163350596100927871725)
    ·
      refine ⟨8571061256473537847951897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22856163350596100927871725 8571061256473537847951897)
      ·
        refine ⟨6428295942355153385963923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8571061256473537847951897 6428295942355153385963923)
        ·
          refine ⟨9642443913532730078945885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6428295942355153385963923 9642443913532730078945885)
          ·
            refine ⟨3615916467574773779604707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9642443913532730078945885 3615916467574773779604707)
            ·
              refine ⟨5423874701362160669407061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3615916467574773779604707 5423874701362160669407061)
              ·
                refine ⟨31780515828293910172307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5423874701362160669407061 31780515828293910172307)
                ·
                  rfl

theorem cell23_1671093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 9].length) (baseStart_1671093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671093 prefixEnd_1671093 := by exact prefixLift 1671093
  have htrace : WordTrace (prefixWord ++ tailWord_1671093) baseStart_1671093 baseEnd_1671093 := by
    simpa [prefixWord, tailWord_1671093, baseEnd_1671093] using wordTrace_append hprefix tailTrace_1671093
  have hstable : (prefixWord ++ tailWord_1671093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671093).length < 2 ^ (prefixWord ++ tailWord_1671093).sum := by decide
  have hdescent : baseEnd_1671093 < baseStart_1671093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671103 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 3]
def baseStart_1671103 : Nat := 118140960795 + 1671103 * 2 ^ 59
def prefixEnd_1671103 : Nat := 4983230072969 + 3 ^ 40 * 1671103 * 2
def baseEnd_1671103 : Nat := 858079062170480535527243

theorem tailTrace_1671103 : CollatzResearch.WordTrace tailWord_1671103 prefixEnd_1671103 858079062170480535527243 := by
  unfold tailWord_1671103
  simp only [CollatzResearch.WordTrace]
  refine ⟨60950133664886707515521963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40633422443257805010347975 60950133664886707515521963)
  ·
    refine ⟨91425200497330061273282945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60950133664886707515521963 91425200497330061273282945)
    ·
      refine ⟨68568900372997545954962209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91425200497330061273282945 68568900372997545954962209)
      ·
        refine ⟨51426675279748159466221657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68568900372997545954962209 51426675279748159466221657)
        ·
          refine ⟨38570006459811119599666243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51426675279748159466221657 38570006459811119599666243)
          ·
            refine ⟨57855009689716679399499365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38570006459811119599666243 57855009689716679399499365)
            ·
              refine ⟨10847814316821877387406131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57855009689716679399499365 10847814316821877387406131)
              ·
                refine ⟨16271721475232816081109197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10847814316821877387406131 16271721475232816081109197)
                ·
                  refine ⟨6101895553212306030415949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16271721475232816081109197 6101895553212306030415949)
                  ·
                    refine ⟨2288210832454614761405981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6101895553212306030415949 2288210832454614761405981)
                    ·
                      refine ⟨858079062170480535527243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2288210832454614761405981 858079062170480535527243)
                      ·
                        rfl

theorem cell23_1671103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_1671103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671103 prefixEnd_1671103 := by exact prefixLift 1671103
  have htrace : WordTrace (prefixWord ++ tailWord_1671103) baseStart_1671103 baseEnd_1671103 := by
    simpa [prefixWord, tailWord_1671103, baseEnd_1671103] using wordTrace_append hprefix tailTrace_1671103
  have hstable : (prefixWord ++ tailWord_1671103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671103).length < 2 ^ (prefixWord ++ tailWord_1671103).sum := by decide
  have hdescent : baseEnd_1671103 < baseStart_1671103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671120 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 4, 1, 3]
def baseStart_1671120 : Nat := 118140960795 + 1671120 * 2 ^ 59
def prefixEnd_1671120 : Nat := 4983230072969 + 3 ^ 40 * 1671120 * 2
def baseEnd_1671120 : Nat := 858087791341606969014665

theorem tailTrace_1671120 : CollatzResearch.WordTrace tailWord_1671120 prefixEnd_1671120 858087791341606969014665 := by
  unfold tailWord_1671120
  simp only [CollatzResearch.WordTrace]
  refine ⟨30475376852912559709445407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40633835803883412945927209 30475376852912559709445407)
  ·
    refine ⟨45713065279368839564168111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30475376852912559709445407 45713065279368839564168111)
    ·
      refine ⟨68569597919053259346252167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45713065279368839564168111 68569597919053259346252167)
      ·
        refine ⟨102854396878579889019378251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68569597919053259346252167 102854396878579889019378251)
        ·
          refine ⟨154281595317869833529067377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102854396878579889019378251 154281595317869833529067377)
          ·
            refine ⟨115711196488402375146800533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154281595317869833529067377 115711196488402375146800533)
            ·
              refine ⟨5423962335393861335006275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115711196488402375146800533 5423962335393861335006275)
              ·
                refine ⟨8135943503090792002509413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423962335393861335006275 8135943503090792002509413)
                ·
                  refine ⟨1525489406829523500470515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8135943503090792002509413 1525489406829523500470515)
                  ·
                    refine ⟨2288234110244285250705773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1525489406829523500470515 2288234110244285250705773)
                    ·
                      refine ⟨858087791341606969014665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2288234110244285250705773 858087791341606969014665)
                      ·
                        rfl

theorem cell23_1671120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 1, 3].length) (baseStart_1671120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671120 prefixEnd_1671120 := by exact prefixLift 1671120
  have htrace : WordTrace (prefixWord ++ tailWord_1671120) baseStart_1671120 baseEnd_1671120 := by
    simpa [prefixWord, tailWord_1671120, baseEnd_1671120] using wordTrace_append hprefix tailTrace_1671120
  have hstable : (prefixWord ++ tailWord_1671120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671120).length < 2 ^ (prefixWord ++ tailWord_1671120).sum := by decide
  have hdescent : baseEnd_1671120 < baseStart_1671120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671160 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 3, 4, 2]
def baseStart_1671160 : Nat := 118140960795 + 1671160 * 2 ^ 59
def prefixEnd_1671160 : Nat := 4983230072969 + 3 ^ 40 * 1671160 * 2
def baseEnd_1671160 : Nat := 858108330567786812514481

theorem tailTrace_1671160 : CollatzResearch.WordTrace tailWord_1671160 prefixEnd_1671160 858108330567786812514481 := by
  unfold tailWord_1671160
  simp only [CollatzResearch.WordTrace]
  refine ⟨30476106312840103125173467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40634808417120137500231289 30476106312840103125173467)
  ·
    refine ⟨45714159469260154687760201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30476106312840103125173467 45714159469260154687760201)
    ·
      refine ⟨34285619601945116015820151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45714159469260154687760201 34285619601945116015820151)
      ·
        refine ⟨51428429402917674023730227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34285619601945116015820151 51428429402917674023730227)
        ·
          refine ⟨77142644104376511035595341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51428429402917674023730227 77142644104376511035595341)
          ·
            refine ⟨28928491539141191638348253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77142644104376511035595341 28928491539141191638348253)
            ·
              refine ⟨10848184327177946864380595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28928491539141191638348253 10848184327177946864380595)
              ·
                refine ⟨16272276490766920296570893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10848184327177946864380595 16272276490766920296570893)
                ·
                  refine ⟨6102103684037595111214085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16272276490766920296570893 6102103684037595111214085)
                  ·
                    refine ⟨1144144440757049083352641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6102103684037595111214085 1144144440757049083352641)
                    ·
                      refine ⟨858108330567786812514481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144144440757049083352641 858108330567786812514481)
                      ·
                        rfl

theorem cell23_1671160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_1671160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671160 prefixEnd_1671160 := by exact prefixLift 1671160
  have htrace : WordTrace (prefixWord ++ tailWord_1671160) baseStart_1671160 baseEnd_1671160 := by
    simpa [prefixWord, tailWord_1671160, baseEnd_1671160] using wordTrace_append hprefix tailTrace_1671160
  have hstable : (prefixWord ++ tailWord_1671160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671160).length < 2 ^ (prefixWord ++ tailWord_1671160).sum := by decide
  have hdescent : baseEnd_1671160 < baseStart_1671160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671163 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 5]
def baseStart_1671163 : Nat := 118140960795 + 1671163 * 2 ^ 59
def prefixEnd_1671163 : Nat := 4983230072969 + 3 ^ 40 * 1671163 * 2
def baseEnd_1671163 : Nat := 858109871009750300776967

theorem tailTrace_1671163 : CollatzResearch.WordTrace tailWord_1671163 prefixEnd_1671163 858109871009750300776967 := by
  unfold tailWord_1671163
  simp only [CollatzResearch.WordTrace]
  refine ⟨60952322044669337762706143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40634881363112891841804095 60952322044669337762706143)
  ·
    refine ⟨91428483067004006644059215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60952322044669337762706143 91428483067004006644059215)
    ·
      refine ⟨137142724600506009966088823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91428483067004006644059215 137142724600506009966088823)
      ·
        refine ⟨205714086900759014949133235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137142724600506009966088823 205714086900759014949133235)
        ·
          refine ⟨308571130351138522423699853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205714086900759014949133235 308571130351138522423699853)
          ·
            refine ⟨115714173881676945908887445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308571130351138522423699853 115714173881676945908887445)
            ·
              refine ⟨5424101900703606839479099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115714173881676945908887445 5424101900703606839479099)
              ·
                refine ⟨8136152851055410259218649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424101900703606839479099 8136152851055410259218649)
                ·
                  refine ⟨6102114638291557694413987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8136152851055410259218649 6102114638291557694413987)
                  ·
                    refine ⟨9153171957437336541620981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102114638291557694413987 9153171957437336541620981)
                    ·
                      refine ⟨858109871009750300776967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9153171957437336541620981 858109871009750300776967)
                      ·
                        rfl

theorem cell23_1671163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 5].length) (baseStart_1671163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671163 prefixEnd_1671163 := by exact prefixLift 1671163
  have htrace : WordTrace (prefixWord ++ tailWord_1671163) baseStart_1671163 baseEnd_1671163 := by
    simpa [prefixWord, tailWord_1671163, baseEnd_1671163] using wordTrace_append hprefix tailTrace_1671163
  have hstable : (prefixWord ++ tailWord_1671163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671163).length < 2 ^ (prefixWord ++ tailWord_1671163).sum := by decide
  have hdescent : baseEnd_1671163 < baseStart_1671163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671164 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_1671164 : Nat := 118140960795 + 1671164 * 2 ^ 59
def prefixEnd_1671164 : Nat := 4983230072969 + 3 ^ 40 * 1671164 * 2
def baseEnd_1671164 : Nat := 858110384490404796864463

theorem tailTrace_1671164 : CollatzResearch.WordTrace tailWord_1671164 prefixEnd_1671164 858110384490404796864463 := by
  unfold tailWord_1671164
  simp only [CollatzResearch.WordTrace]
  refine ⟨30476179258832857466746273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40634905678443809955661697 30476179258832857466746273)
  ·
    refine ⟨22857134444124643100059705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30476179258832857466746273 22857134444124643100059705)
    ·
      refine ⟨17142850833093482325044779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22857134444124643100059705 17142850833093482325044779)
      ·
        refine ⟨25714276249640223487567169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17142850833093482325044779 25714276249640223487567169)
        ·
          refine ⟨19285707187230167615675377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25714276249640223487567169 19285707187230167615675377)
          ·
            refine ⟨14464280390422625711756533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19285707187230167615675377 14464280390422625711756533)
            ·
              refine ⟨1356026286602121160477175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14464280390422625711756533 1356026286602121160477175)
              ·
                refine ⟨2034039429903181740715763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356026286602121160477175 2034039429903181740715763)
                ·
                  refine ⟨3051059144854772611073645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034039429903181740715763 3051059144854772611073645)
                  ·
                    refine ⟨1144147179320539729152617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3051059144854772611073645 1144147179320539729152617)
                    ·
                      refine ⟨858110384490404796864463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144147179320539729152617 858110384490404796864463)
                      ·
                        rfl

theorem cell23_1671164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_1671164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671164 prefixEnd_1671164 := by exact prefixLift 1671164
  have htrace : WordTrace (prefixWord ++ tailWord_1671164) baseStart_1671164 baseEnd_1671164 := by
    simpa [prefixWord, tailWord_1671164, baseEnd_1671164] using wordTrace_append hprefix tailTrace_1671164
  have hstable : (prefixWord ++ tailWord_1671164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671164).length < 2 ^ (prefixWord ++ tailWord_1671164).sum := by decide
  have hdescent : baseEnd_1671164 < baseStart_1671164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671172 : List Nat := [2, 3, 2, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1671172 : Nat := 118140960795 + 1671172 * 2 ^ 59
def prefixEnd_1671172 : Nat := 4983230072969 + 3 ^ 40 * 1671172 * 2
def baseEnd_1671172 : Nat := 858114492335640765564427

theorem tailTrace_1671172 : CollatzResearch.WordTrace tailWord_1671172 prefixEnd_1671172 858114492335640765564427 := by
  unfold tailWord_1671172
  simp only [CollatzResearch.WordTrace]
  refine ⟨30476325150818366149891885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40635100201091154866522513 30476325150818366149891885)
  ·
    refine ⟨11428621931556887306209457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30476325150818366149891885 11428621931556887306209457)
    ·
      refine ⟨8571466448667665479657093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11428621931556887306209457 8571466448667665479657093)
      ·
        refine ⟨1607149959125187277435705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8571466448667665479657093 1607149959125187277435705)
        ·
          refine ⟨1205362469343890458076779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1607149959125187277435705 1205362469343890458076779)
          ·
            refine ⟨1808043704015835687115169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205362469343890458076779 1808043704015835687115169)
            ·
              refine ⟨1356032778011876765336377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808043704015835687115169 1356032778011876765336377)
              ·
                refine ⟨1017024583508907574002283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356032778011876765336377 1017024583508907574002283)
                ·
                  refine ⟨1525536875263361361003425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017024583508907574002283 1525536875263361361003425)
                  ·
                    refine ⟨1144152656447521020752569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1525536875263361361003425 1144152656447521020752569)
                    ·
                      refine ⟨858114492335640765564427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144152656447521020752569 858114492335640765564427)
                      ·
                        rfl

theorem cell23_1671172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1671172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671172 prefixEnd_1671172 := by exact prefixLift 1671172
  have htrace : WordTrace (prefixWord ++ tailWord_1671172) baseStart_1671172 baseEnd_1671172 := by
    simpa [prefixWord, tailWord_1671172, baseEnd_1671172] using wordTrace_append hprefix tailTrace_1671172
  have hstable : (prefixWord ++ tailWord_1671172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671172).length < 2 ^ (prefixWord ++ tailWord_1671172).sum := by decide
  have hdescent : baseEnd_1671172 < baseStart_1671172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671194 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2]
def baseStart_1671194 : Nat := 118140960795 + 1671194 * 2 ^ 59
def prefixEnd_1671194 : Nat := 4983230072969 + 3 ^ 40 * 1671194 * 2
def baseEnd_1671194 : Nat := 858125788910039679489325

theorem tailTrace_1671194 : CollatzResearch.WordTrace tailWord_1671194 prefixEnd_1671194 858125788910039679489325 := by
  unfold tailWord_1671194
  simp only [CollatzResearch.WordTrace]
  refine ⟨15238363176889257514271159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40635635138371353371389757 15238363176889257514271159)
  ·
    refine ⟨22857544765333886271406739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15238363176889257514271159 22857544765333886271406739)
    ·
      refine ⟨34286317148000829407110109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22857544765333886271406739 34286317148000829407110109)
      ·
        refine ⟨12857368930500311027666291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34286317148000829407110109 12857368930500311027666291)
        ·
          refine ⟨19286053395750466541499437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12857368930500311027666291 19286053395750466541499437)
          ·
            refine ⟨7232270023406424953062289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19286053395750466541499437 7232270023406424953062289)
            ·
              refine ⟨5424202517554818714796717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7232270023406424953062289 5424202517554818714796717)
              ·
                refine ⟨2034075944083057018048769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5424202517554818714796717 2034075944083057018048769)
                ·
                  refine ⟨1525556958062292763536577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2034075944083057018048769 1525556958062292763536577)
                  ·
                    refine ⟨1144167718546719572652433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1525556958062292763536577 1144167718546719572652433)
                    ·
                      refine ⟨858125788910039679489325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144167718546719572652433 858125788910039679489325)
                      ·
                        rfl

theorem cell23_1671194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_1671194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671194 prefixEnd_1671194 := by exact prefixLift 1671194
  have htrace : WordTrace (prefixWord ++ tailWord_1671194) baseStart_1671194 baseEnd_1671194 := by
    simpa [prefixWord, tailWord_1671194, baseEnd_1671194] using wordTrace_append hprefix tailTrace_1671194
  have hstable : (prefixWord ++ tailWord_1671194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671194).length < 2 ^ (prefixWord ++ tailWord_1671194).sum := by decide
  have hdescent : baseEnd_1671194 < baseStart_1671194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671217 : List Nat := [1, 2, 2, 3, 1, 4, 2, 3, 5]
def baseStart_1671217 : Nat := 118140960795 + 1671217 * 2 ^ 59
def prefixEnd_1671217 : Nat := 4983230072969 + 3 ^ 40 * 1671217 * 2
def baseEnd_1671217 : Nat := 95348622107232565500191

theorem tailTrace_1671217 : CollatzResearch.WordTrace tailWord_1671217 prefixEnd_1671217 95348622107232565500191 := by
  unfold tailWord_1671217
  simp only [CollatzResearch.WordTrace]
  refine ⟨60954291586473704985171905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40636194390982469990114603 60954291586473704985171905)
  ·
    refine ⟨45715718689855278738878929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60954291586473704985171905 45715718689855278738878929)
    ·
      refine ⟨34286789017391459054159197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45715718689855278738878929 34286789017391459054159197)
      ·
        refine ⟨12857545881521797145309699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34286789017391459054159197 12857545881521797145309699)
        ·
          refine ⟨19286318822282695717964549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12857545881521797145309699 19286318822282695717964549)
          ·
            refine ⟨3616184779178005447118353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19286318822282695717964549 3616184779178005447118353)
            ·
              refine ⟨2712138584383504085338765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3616184779178005447118353 2712138584383504085338765)
              ·
                refine ⟨1017051969143814032002037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2712138584383504085338765 1017051969143814032002037)
                ·
                  refine ⟨95348622107232565500191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1017051969143814032002037 95348622107232565500191)
                  ·
                    rfl

theorem cell23_1671217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 5].length) (baseStart_1671217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671217 prefixEnd_1671217 := by exact prefixLift 1671217
  have htrace : WordTrace (prefixWord ++ tailWord_1671217) baseStart_1671217 baseEnd_1671217 := by
    simpa [prefixWord, tailWord_1671217, baseEnd_1671217] using wordTrace_append hprefix tailTrace_1671217
  have hstable : (prefixWord ++ tailWord_1671217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671217).length < 2 ^ (prefixWord ++ tailWord_1671217).sum := by decide
  have hdescent : baseEnd_1671217 < baseStart_1671217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671223 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1671223 : Nat := 118140960795 + 1671223 * 2 ^ 59
def prefixEnd_1671223 : Nat := 4983230072969 + 3 ^ 40 * 1671223 * 2
def baseEnd_1671223 : Nat := 858140679849020066026691

theorem tailTrace_1671223 : CollatzResearch.WordTrace tailWord_1671223 prefixEnd_1671223 858140679849020066026691 := by
  unfold tailWord_1671223
  simp only [CollatzResearch.WordTrace]
  refine ⟨60954510424451968009890323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40636340282967978673260215 60954510424451968009890323)
  ·
    refine ⟨91431765636677952014835485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60954510424451968009890323 91431765636677952014835485)
    ·
      refine ⟨34286912113754232005563307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91431765636677952014835485 34286912113754232005563307)
      ·
        refine ⟨51430368170631348008344961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34286912113754232005563307 51430368170631348008344961)
        ·
          refine ⟨38572776127973511006258721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51430368170631348008344961 38572776127973511006258721)
          ·
            refine ⟨28929582095980133254694041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38572776127973511006258721 28929582095980133254694041)
            ·
              refine ⟨21697186571985099941020531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28929582095980133254694041 21697186571985099941020531)
              ·
                refine ⟨32545779857977649911530797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21697186571985099941020531 32545779857977649911530797)
                ·
                  refine ⟨12204667446741618716824049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32545779857977649911530797 12204667446741618716824049)
                  ·
                    refine ⟨9153500585056214037618037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12204667446741618716824049 9153500585056214037618037)
                    ·
                      refine ⟨858140679849020066026691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9153500585056214037618037 858140679849020066026691)
                      ·
                        rfl

theorem cell23_1671223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1671223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671223 prefixEnd_1671223 := by exact prefixLift 1671223
  have htrace : WordTrace (prefixWord ++ tailWord_1671223) baseStart_1671223 baseEnd_1671223 := by
    simpa [prefixWord, tailWord_1671223, baseEnd_1671223] using wordTrace_append hprefix tailTrace_1671223
  have hstable : (prefixWord ++ tailWord_1671223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671223).length < 2 ^ (prefixWord ++ tailWord_1671223).sum := by decide
  have hdescent : baseEnd_1671223 < baseStart_1671223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671263 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1671263 : Nat := 118140960795 + 1671263 * 2 ^ 59
def prefixEnd_1671263 : Nat := 4983230072969 + 3 ^ 40 * 1671263 * 2
def baseEnd_1671263 : Nat := 858161219075199909526507

theorem tailTrace_1671263 : CollatzResearch.WordTrace tailWord_1671263 prefixEnd_1671263 858161219075199909526507 := by
  unfold tailWord_1671263
  simp only [CollatzResearch.WordTrace]
  refine ⟨60955969344307054841346443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40637312896204703227564295 60955969344307054841346443)
  ·
    refine ⟨91433954016460582262019665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60955969344307054841346443 91433954016460582262019665)
    ·
      refine ⟨68575465512345436696514749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91433954016460582262019665 68575465512345436696514749)
      ·
        refine ⟨25715799567129538761193031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68575465512345436696514749 25715799567129538761193031)
        ·
          refine ⟨38573699350694308141789547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25715799567129538761193031 38573699350694308141789547)
          ·
            refine ⟨57860549026041462212684321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38573699350694308141789547 57860549026041462212684321)
            ·
              refine ⟨43395411769531096659513241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57860549026041462212684321 43395411769531096659513241)
              ·
                refine ⟨32546558827148322494634931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43395411769531096659513241 32546558827148322494634931)
                ·
                  refine ⟨48819838240722483741952397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32546558827148322494634931 48819838240722483741952397)
                  ·
                    refine ⟨18307439340270931403232149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48819838240722483741952397 18307439340270931403232149)
                    ·
                      refine ⟨858161219075199909526507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18307439340270931403232149 858161219075199909526507)
                      ·
                        rfl

theorem cell23_1671263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1671263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671263 prefixEnd_1671263 := by exact prefixLift 1671263
  have htrace : WordTrace (prefixWord ++ tailWord_1671263) baseStart_1671263 baseEnd_1671263 := by
    simpa [prefixWord, tailWord_1671263, baseEnd_1671263] using wordTrace_append hprefix tailTrace_1671263
  have hstable : (prefixWord ++ tailWord_1671263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671263).length < 2 ^ (prefixWord ++ tailWord_1671263).sum := by decide
  have hdescent : baseEnd_1671263 < baseStart_1671263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671273 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 10]
def baseStart_1671273 : Nat := 118140960795 + 1671273 * 2 ^ 59
def prefixEnd_1671273 : Nat := 4983230072969 + 3 ^ 40 * 1671273 * 2
def baseEnd_1671273 : Nat := 95351817097971652266829

theorem tailTrace_1671273 : CollatzResearch.WordTrace tailWord_1671273 prefixEnd_1671273 95351817097971652266829 := by
  unfold tailWord_1671273
  simp only [CollatzResearch.WordTrace]
  refine ⟨60956334074270826549210473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40637556049513884366140315 60956334074270826549210473)
  ·
    refine ⟨45717250555703119911907855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60956334074270826549210473 45717250555703119911907855)
    ·
      refine ⟨68575875833554679867861783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45717250555703119911907855 68575875833554679867861783)
      ·
        refine ⟨102863813750332019801792675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68575875833554679867861783 102863813750332019801792675)
        ·
          refine ⟨154295720625498029702689013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102863813750332019801792675 154295720625498029702689013)
          ·
            refine ⟨14465223808640440284627095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154295720625498029702689013 14465223808640440284627095)
            ·
              refine ⟨21697835712960660426940643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14465223808640440284627095 21697835712960660426940643)
              ·
                refine ⟨32546753569440990640410965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21697835712960660426940643 32546753569440990640410965)
                ·
                  refine ⟨95351817097971652266829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 32546753569440990640410965 95351817097971652266829)
                  ·
                    rfl

theorem cell23_1671273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 10].length) (baseStart_1671273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671273 prefixEnd_1671273 := by exact prefixLift 1671273
  have htrace : WordTrace (prefixWord ++ tailWord_1671273) baseStart_1671273 baseEnd_1671273 := by
    simpa [prefixWord, tailWord_1671273, baseEnd_1671273] using wordTrace_append hprefix tailTrace_1671273
  have hstable : (prefixWord ++ tailWord_1671273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671273).length < 2 ^ (prefixWord ++ tailWord_1671273).sum := by decide
  have hdescent : baseEnd_1671273 < baseStart_1671273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671287 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_1671287 : Nat := 118140960795 + 1671287 * 2 ^ 59
def prefixEnd_1671287 : Nat := 4983230072969 + 3 ^ 40 * 1671287 * 2
def baseEnd_1671287 : Nat := 858173542610907815626397

theorem tailTrace_1671287 : CollatzResearch.WordTrace tailWord_1671287 prefixEnd_1671287 858173542610907815626397 := by
  unfold tailWord_1671287
  simp only [CollatzResearch.WordTrace]
  refine ⟨60956844696220106940220115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40637896464146737960146743 60956844696220106940220115)
  ·
    refine ⟨91435267044330160410330173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60956844696220106940220115 91435267044330160410330173)
    ·
      refine ⟨34288225141623810153873815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91435267044330160410330173 34288225141623810153873815)
      ·
        refine ⟨51432337712435715230810723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34288225141623810153873815 51432337712435715230810723)
        ·
          refine ⟨77148506568653572846216085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51432337712435715230810723 77148506568653572846216085)
          ·
            refine ⟨3616336245405636227166379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77148506568653572846216085 3616336245405636227166379)
            ·
              refine ⟨5424504368108454340749569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616336245405636227166379 5424504368108454340749569)
              ·
                refine ⟨4068378276081340755562177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5424504368108454340749569 4068378276081340755562177)
                ·
                  refine ⟨3051283707061005566671633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4068378276081340755562177 3051283707061005566671633)
                  ·
                    refine ⟨2288462780295754175003725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3051283707061005566671633 2288462780295754175003725)
                    ·
                      refine ⟨858173542610907815626397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2288462780295754175003725 858173542610907815626397)
                      ·
                        rfl

theorem cell23_1671287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_1671287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671287 prefixEnd_1671287 := by exact prefixLift 1671287
  have htrace : WordTrace (prefixWord ++ tailWord_1671287) baseStart_1671287 baseEnd_1671287 := by
    simpa [prefixWord, tailWord_1671287, baseEnd_1671287] using wordTrace_append hprefix tailTrace_1671287
  have hstable : (prefixWord ++ tailWord_1671287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671287).length < 2 ^ (prefixWord ++ tailWord_1671287).sum := by decide
  have hdescent : baseEnd_1671287 < baseStart_1671287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671317 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_1671317 : Nat := 118140960795 + 1671317 * 2 ^ 59
def prefixEnd_1671317 : Nat := 4983230072969 + 3 ^ 40 * 1671317 * 2
def baseEnd_1671317 : Nat := 858188947030542698251259

theorem tailTrace_1671317 : CollatzResearch.WordTrace tailWord_1671317 prefixEnd_1671317 858188947030542698251259 := by
  unfold tailWord_1671317
  simp only [CollatzResearch.WordTrace]
  refine ⟨60957938886111422063812205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40638625924074281375874803 60957938886111422063812205)
  ·
    refine ⟨22859227082291783273929577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60957938886111422063812205 22859227082291783273929577)
    ·
      refine ⟨17144420311718837455447183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22859227082291783273929577 17144420311718837455447183)
      ·
        refine ⟨25716630467578256183170775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17144420311718837455447183 25716630467578256183170775)
        ·
          refine ⟨38574945701367384274756163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25716630467578256183170775 38574945701367384274756163)
          ·
            refine ⟨57862418552051076412134245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38574945701367384274756163 57862418552051076412134245)
            ·
              refine ⟨10849203478509576827275171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57862418552051076412134245 10849203478509576827275171)
              ·
                refine ⟨16273805217764365240912757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10849203478509576827275171 16273805217764365240912757)
                ·
                  refine ⟨1525669239165409241335571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16273805217764365240912757 1525669239165409241335571)
                  ·
                    refine ⟨2288503858748113862003357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1525669239165409241335571 2288503858748113862003357)
                    ·
                      refine ⟨858188947030542698251259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2288503858748113862003357 858188947030542698251259)
                      ·
                        rfl

theorem cell23_1671317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_1671317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671317 prefixEnd_1671317 := by exact prefixLift 1671317
  have htrace : WordTrace (prefixWord ++ tailWord_1671317) baseStart_1671317 baseEnd_1671317 := by
    simpa [prefixWord, tailWord_1671317, baseEnd_1671317] using wordTrace_append hprefix tailTrace_1671317
  have hstable : (prefixWord ++ tailWord_1671317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671317).length < 2 ^ (prefixWord ++ tailWord_1671317).sum := by decide
  have hdescent : baseEnd_1671317 < baseStart_1671317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671345 : List Nat := [1, 2, 2, 5, 3, 1, 2, 2, 1, 4]
def baseStart_1671345 : Nat := 118140960795 + 1671345 * 2 ^ 59
def prefixEnd_1671345 : Nat := 4983230072969 + 3 ^ 40 * 1671345 * 2
def baseEnd_1671345 : Nat := 286067774829622862900377

theorem tailTrace_1671345 : CollatzResearch.WordTrace tailWord_1671345 prefixEnd_1671345 286067774829622862900377 := by
  unfold tailWord_1671345
  simp only [CollatzResearch.WordTrace]
  refine ⟨60958960130009982845831489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40639306753339988563887659 60958960130009982845831489)
  ·
    refine ⟨45719220097507487134373617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60958960130009982845831489 45719220097507487134373617)
    ·
      refine ⟨34289415073130615350780213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45719220097507487134373617 34289415073130615350780213)
      ·
        refine ⟨3214632663105995189135645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34289415073130615350780213 3214632663105995189135645)
        ·
          refine ⟨1205487248664748195925867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3214632663105995189135645 1205487248664748195925867)
          ·
            refine ⟨1808230872997122293888801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205487248664748195925867 1808230872997122293888801)
            ·
              refine ⟨1356173154747841720416601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808230872997122293888801 1356173154747841720416601)
              ·
                refine ⟨1017129866060881290312451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356173154747841720416601 1017129866060881290312451)
                ·
                  refine ⟨1525694799091321935468677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017129866060881290312451 1525694799091321935468677)
                  ·
                    refine ⟨286067774829622862900377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1525694799091321935468677 286067774829622862900377)
                    ·
                      rfl

theorem cell23_1671345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_1671345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671345 prefixEnd_1671345 := by exact prefixLift 1671345
  have htrace : WordTrace (prefixWord ++ tailWord_1671345) baseStart_1671345 baseEnd_1671345 := by
    simpa [prefixWord, tailWord_1671345, baseEnd_1671345] using wordTrace_append hprefix tailTrace_1671345
  have hstable : (prefixWord ++ tailWord_1671345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671345).length < 2 ^ (prefixWord ++ tailWord_1671345).sum := by decide
  have hdescent : baseEnd_1671345 < baseStart_1671345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671351 : List Nat := [1, 1, 3, 1, 4, 3, 1, 4, 1, 1, 3]
def baseStart_1671351 : Nat := 118140960795 + 1671351 * 2 ^ 59
def prefixEnd_1671351 : Nat := 4983230072969 + 3 ^ 40 * 1671351 * 2
def baseEnd_1671351 : Nat := 858206405372795565226103

theorem tailTrace_1671351 : CollatzResearch.WordTrace tailWord_1671351 prefixEnd_1671351 858206405372795565226103 := by
  unfold tailWord_1671351
  simp only [CollatzResearch.WordTrace]
  refine ⟨60959178967988245870549907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40639452645325497247033271 60959178967988245870549907)
  ·
    refine ⟨91438768451982368805824861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60959178967988245870549907 91438768451982368805824861)
    ·
      refine ⟨34289538169493388302184323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91438768451982368805824861 34289538169493388302184323)
      ·
        refine ⟨51434307254240082453276485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34289538169493388302184323 51434307254240082453276485)
        ·
          refine ⟨9643932610170015459989341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51434307254240082453276485 9643932610170015459989341)
          ·
            refine ⟨3616474728813755797496003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9643932610170015459989341 3616474728813755797496003)
            ·
              refine ⟨5424712093220633696244005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616474728813755797496003 5424712093220633696244005)
              ·
                refine ⟨1017133517478868818045751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5424712093220633696244005 1017133517478868818045751)
                ·
                  refine ⟨1525700276218303227068627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017133517478868818045751 1525700276218303227068627)
                  ·
                    refine ⟨2288550414327454840602941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1525700276218303227068627 2288550414327454840602941)
                    ·
                      refine ⟨858206405372795565226103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2288550414327454840602941 858206405372795565226103)
                      ·
                        rfl

theorem cell23_1671351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 1, 3].length) (baseStart_1671351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671351 prefixEnd_1671351 := by exact prefixLift 1671351
  have htrace : WordTrace (prefixWord ++ tailWord_1671351) baseStart_1671351 baseEnd_1671351 := by
    simpa [prefixWord, tailWord_1671351, baseEnd_1671351] using wordTrace_append hprefix tailTrace_1671351
  have hstable : (prefixWord ++ tailWord_1671351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671351).length < 2 ^ (prefixWord ++ tailWord_1671351).sum := by decide
  have hdescent : baseEnd_1671351 < baseStart_1671351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671357 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_1671357 : Nat := 118140960795 + 1671357 * 2 ^ 59
def prefixEnd_1671357 : Nat := 4983230072969 + 3 ^ 40 * 1671357 * 2
def baseEnd_1671357 : Nat := 858209486256722541751075

theorem tailTrace_1671357 : CollatzResearch.WordTrace tailWord_1671357 prefixEnd_1671357 858209486256722541751075 := by
  unfold tailWord_1671357
  simp only [CollatzResearch.WordTrace]
  refine ⟨60959397805966508895268325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40639598537311005930178883 60959397805966508895268325)
  ·
    refine ⟨11429887088618720417862811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60959397805966508895268325 11429887088618720417862811)
    ·
      refine ⟨17144830632928080626794217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11429887088618720417862811 17144830632928080626794217)
      ·
        refine ⟨12858622974696060470095663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17144830632928080626794217 12858622974696060470095663)
        ·
          refine ⟨19287934462044090705143495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12858622974696060470095663 19287934462044090705143495)
          ·
            refine ⟨28931901693066136057715243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19287934462044090705143495 28931901693066136057715243)
            ·
              refine ⟨43397852539599204086572865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28931901693066136057715243 43397852539599204086572865)
              ·
                refine ⟨32548389404699403064929649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43397852539599204086572865 32548389404699403064929649)
                ·
                  refine ⟨24411292053524552298697237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32548389404699403064929649 24411292053524552298697237)
                  ·
                    refine ⟨1144279315008963389001433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24411292053524552298697237 1144279315008963389001433)
                    ·
                      refine ⟨858209486256722541751075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144279315008963389001433 858209486256722541751075)
                      ·
                        rfl

theorem cell23_1671357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_1671357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671357 prefixEnd_1671357 := by exact prefixLift 1671357
  have htrace : WordTrace (prefixWord ++ tailWord_1671357) baseStart_1671357 baseEnd_1671357 := by
    simpa [prefixWord, tailWord_1671357, baseEnd_1671357] using wordTrace_append hprefix tailTrace_1671357
  have hstable : (prefixWord ++ tailWord_1671357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671357).length < 2 ^ (prefixWord ++ tailWord_1671357).sum := by decide
  have hdescent : baseEnd_1671357 < baseStart_1671357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671377 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_1671377 : Nat := 118140960795 + 1671377 * 2 ^ 59
def prefixEnd_1671377 : Nat := 4983230072969 + 3 ^ 40 * 1671377 * 2
def baseEnd_1671377 : Nat := 858219755869812463500983

theorem tailTrace_1671377 : CollatzResearch.WordTrace tailWord_1671377 prefixEnd_1671377 858219755869812463500983 := by
  unfold tailWord_1671377
  simp only [CollatzResearch.WordTrace]
  refine ⟨60960127265894052310996385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40640084843929368207330923 60960127265894052310996385)
  ·
    refine ⟨45720095449420539233247289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60960127265894052310996385 45720095449420539233247289)
    ·
      refine ⟨34290071587065404424935467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45720095449420539233247289 34290071587065404424935467)
      ·
        refine ⟨51435107380598106637403201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34290071587065404424935467 51435107380598106637403201)
        ·
          refine ⟨38576330535448579978052401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51435107380598106637403201 38576330535448579978052401)
          ·
            refine ⟨28932247901586434983539301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38576330535448579978052401 28932247901586434983539301)
            ·
              refine ⟨5424796481547456559413619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28932247901586434983539301 5424796481547456559413619)
              ·
                refine ⟨8137194722321184839120429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424796481547456559413619 8137194722321184839120429)
                ·
                  refine ⟨3051448020870444314670161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8137194722321184839120429 3051448020870444314670161)
                  ·
                    refine ⟨2288586015652833236002621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3051448020870444314670161 2288586015652833236002621)
                    ·
                      refine ⟨858219755869812463500983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2288586015652833236002621 858219755869812463500983)
                      ·
                        rfl

theorem cell23_1671377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_1671377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671377 prefixEnd_1671377 := by exact prefixLift 1671377
  have htrace : WordTrace (prefixWord ++ tailWord_1671377) baseStart_1671377 baseEnd_1671377 := by
    simpa [prefixWord, tailWord_1671377, baseEnd_1671377] using wordTrace_append hprefix tailTrace_1671377
  have hstable : (prefixWord ++ tailWord_1671377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671377).length < 2 ^ (prefixWord ++ tailWord_1671377).sum := by decide
  have hdescent : baseEnd_1671377 < baseStart_1671377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671417 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 2, 7, 2]
def baseStart_1671417 : Nat := 118140960795 + 1671417 * 2 ^ 59
def prefixEnd_1671417 : Nat := 4983230072969 + 3 ^ 40 * 1671417 * 2
def baseEnd_1671417 : Nat := 858240295095992307000799

theorem tailTrace_1671417 : CollatzResearch.WordTrace tailWord_1671417 prefixEnd_1671417 858240295095992307000799 := by
  unfold tailWord_1671417
  simp only [CollatzResearch.WordTrace]
  refine ⟨60961586185749139142452505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40641057457166092761635003 60961586185749139142452505)
  ·
    refine ⟨45721189639311854356839379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60961586185749139142452505 45721189639311854356839379)
    ·
      refine ⟨68581784458967781535259069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45721189639311854356839379 68581784458967781535259069)
      ·
        refine ⟨25718169172112918075722151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68581784458967781535259069 25718169172112918075722151)
        ·
          refine ⟨38577253758169377113583227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25718169172112918075722151 38577253758169377113583227)
          ·
            refine ⟨57865880637254065670374841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38577253758169377113583227 57865880637254065670374841)
            ·
              refine ⟨43399410477940549252781131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57865880637254065670374841 43399410477940549252781131)
              ·
                refine ⟨65099115716910823879171697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43399410477940549252781131 65099115716910823879171697)
                ·
                  refine ⟨48824336787683117909378773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65099115716910823879171697 48824336787683117909378773)
                  ·
                    refine ⟨1144320393461323076001065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48824336787683117909378773 1144320393461323076001065)
                    ·
                      refine ⟨858240295095992307000799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144320393461323076001065 858240295095992307000799)
                      ·
                        rfl

theorem cell23_1671417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_1671417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671417 prefixEnd_1671417 := by exact prefixLift 1671417
  have htrace : WordTrace (prefixWord ++ tailWord_1671417) baseStart_1671417 baseEnd_1671417 := by
    simpa [prefixWord, tailWord_1671417, baseEnd_1671417] using wordTrace_append hprefix tailTrace_1671417
  have hstable : (prefixWord ++ tailWord_1671417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671417).length < 2 ^ (prefixWord ++ tailWord_1671417).sum := by decide
  have hdescent : baseEnd_1671417 < baseStart_1671417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671424 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 2, 1, 3]
def baseStart_1671424 : Nat := 118140960795 + 1671424 * 2 ^ 59
def prefixEnd_1671424 : Nat := 4983230072969 + 3 ^ 40 * 1671424 * 2
def baseEnd_1671424 : Nat := 858243889460573779613267

theorem tailTrace_1671424 : CollatzResearch.WordTrace tailWord_1671424 prefixEnd_1671424 858243889460573779613267 := by
  unfold tailWord_1671424
  simp only [CollatzResearch.WordTrace]
  refine ⟨30480920748361889668978663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40641227664482519558638217 30480920748361889668978663)
  ·
    refine ⟨45721381122542834503467995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30480920748361889668978663 45721381122542834503467995)
    ·
      refine ⟨68582071683814251755201993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45721381122542834503467995 68582071683814251755201993)
      ·
        refine ⟨51436553762860688816401495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68582071683814251755201993 51436553762860688816401495)
        ·
          refine ⟨77154830644291033224602243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51436553762860688816401495 77154830644291033224602243)
          ·
            refine ⟨115732245966436549836903365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77154830644291033224602243 115732245966436549836903365)
            ·
              refine ⟨21699796118706853094419381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115732245966436549836903365 21699796118706853094419381)
              ·
                refine ⟨2034355886128767477601817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21699796118706853094419381 2034355886128767477601817)
                ·
                  refine ⟨1525766914596575608201363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2034355886128767477601817 1525766914596575608201363)
                  ·
                    refine ⟨2288650371894863412302045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1525766914596575608201363 2288650371894863412302045)
                    ·
                      refine ⟨858243889460573779613267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2288650371894863412302045 858243889460573779613267)
                      ·
                        rfl

theorem cell23_1671424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_1671424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671424 prefixEnd_1671424 := by exact prefixLift 1671424
  have htrace : WordTrace (prefixWord ++ tailWord_1671424) baseStart_1671424 baseEnd_1671424 := by
    simpa [prefixWord, tailWord_1671424, baseEnd_1671424] using wordTrace_append hprefix tailTrace_1671424
  have hstable : (prefixWord ++ tailWord_1671424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671424).length < 2 ^ (prefixWord ++ tailWord_1671424).sum := by decide
  have hdescent : baseEnd_1671424 < baseStart_1671424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671431 : List Nat := [1, 1, 4, 5, 1, 2, 2, 7]
def baseStart_1671431 : Nat := 118140960795 + 1671431 * 2 ^ 59
def prefixEnd_1671431 : Nat := 4983230072969 + 3 ^ 40 * 1671431 * 2
def baseEnd_1671431 : Nat := 31786943845376120452805

theorem tailTrace_1671431 : CollatzResearch.WordTrace tailWord_1671431 prefixEnd_1671431 31786943845376120452805 := by
  unfold tailWord_1671431
  simp only [CollatzResearch.WordTrace]
  refine ⟨60962096807698419533462147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40641397871798946355641431 60962096807698419533462147)
  ·
    refine ⟨91443145211547629300193221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60962096807698419533462147 91443145211547629300193221)
    ·
      refine ⟨17145589727165180493786229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91443145211547629300193221 17145589727165180493786229)
      ·
        refine ⟨1607399036921735671292459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17145589727165180493786229 1607399036921735671292459)
        ·
          refine ⟨2411098555382603506938689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607399036921735671292459 2411098555382603506938689)
          ·
            refine ⟨1808323916536952630204017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2411098555382603506938689 1808323916536952630204017)
            ·
              refine ⟨1356242937402714472653013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808323916536952630204017 1356242937402714472653013)
              ·
                refine ⟨31786943845376120452805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1356242937402714472653013 31786943845376120452805)
                ·
                  rfl

theorem cell23_1671431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 7].length) (baseStart_1671431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671431 prefixEnd_1671431 := by exact prefixLift 1671431
  have htrace : WordTrace (prefixWord ++ tailWord_1671431) baseStart_1671431 baseEnd_1671431 := by
    simpa [prefixWord, tailWord_1671431, baseEnd_1671431] using wordTrace_append hprefix tailTrace_1671431
  have hstable : (prefixWord ++ tailWord_1671431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671431).length < 2 ^ (prefixWord ++ tailWord_1671431).sum := by decide
  have hdescent : baseEnd_1671431 < baseStart_1671431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671434 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_1671434 : Nat := 118140960795 + 1671434 * 2 ^ 59
def prefixEnd_1671434 : Nat := 4983230072969 + 3 ^ 40 * 1671434 * 2
def baseEnd_1671434 : Nat := 858249024267118740488221

theorem tailTrace_1671434 : CollatzResearch.WordTrace tailWord_1671434 prefixEnd_1671434 858249024267118740488221 := by
  unfold tailWord_1671434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15240551556671887761455339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40641470817791700697214237 15240551556671887761455339)
  ·
    refine ⟨22860827335007831642183009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15240551556671887761455339 22860827335007831642183009)
    ·
      refine ⟨17145620501255873731637257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22860827335007831642183009 17145620501255873731637257)
      ·
        refine ⟨12859215375941905298727943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17145620501255873731637257 12859215375941905298727943)
        ·
          refine ⟨19288823063912857948091915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12859215375941905298727943 19288823063912857948091915)
          ·
            refine ⟨28933234595869286922137873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19288823063912857948091915 28933234595869286922137873)
            ·
              refine ⟨21699925946901965191603405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28933234595869286922137873 21699925946901965191603405)
              ·
                refine ⟨8137472230088236946851277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21699925946901965191603405 8137472230088236946851277)
                ·
                  refine ⟨3051552086283088855069229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8137472230088236946851277 3051552086283088855069229)
                  ·
                    refine ⟨1144332032356158320650961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3051552086283088855069229 1144332032356158320650961)
                    ·
                      refine ⟨858249024267118740488221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144332032356158320650961 858249024267118740488221)
                      ·
                        rfl

theorem cell23_1671434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_1671434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671434 prefixEnd_1671434 := by exact prefixLift 1671434
  have htrace : WordTrace (prefixWord ++ tailWord_1671434) baseStart_1671434 baseEnd_1671434 := by
    simpa [prefixWord, tailWord_1671434, baseEnd_1671434] using wordTrace_append hprefix tailTrace_1671434
  have hstable : (prefixWord ++ tailWord_1671434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671434).length < 2 ^ (prefixWord ++ tailWord_1671434).sum := by decide
  have hdescent : baseEnd_1671434 < baseStart_1671434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671477 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1671477 : Nat := 118140960795 + 1671477 * 2 ^ 59
def prefixEnd_1671477 : Nat := 4983230072969 + 3 ^ 40 * 1671477 * 2
def baseEnd_1671477 : Nat := 858271103935262072250523

theorem tailTrace_1671477 : CollatzResearch.WordTrace tailWord_1671477 prefixEnd_1671477 858271103935262072250523 := by
  unfold tailWord_1671477
  simp only [CollatzResearch.WordTrace]
  refine ⟨60963774565531769389636685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40642516377021179593091123 60963774565531769389636685)
  ·
    refine ⟨22861415462074413521113757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60963774565531769389636685 22861415462074413521113757)
    ·
      refine ⟨8573030798277905070417659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22861415462074413521113757 8573030798277905070417659)
      ·
        refine ⟨12859546197416857605626489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8573030798277905070417659 12859546197416857605626489)
        ·
          refine ⟨9644659648062643204219867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12859546197416857605626489 9644659648062643204219867)
          ·
            refine ⟨14466989472093964806329801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9644659648062643204219867 14466989472093964806329801)
            ·
              refine ⟨10850242104070473604747351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14466989472093964806329801 10850242104070473604747351)
              ·
                refine ⟨16275363156105710407121027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10850242104070473604747351 16275363156105710407121027)
                ·
                  refine ⟨24413044734158565610681541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16275363156105710407121027 24413044734158565610681541)
                  ·
                    refine ⟨4577445887654731052002789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24413044734158565610681541 4577445887654731052002789)
                    ·
                      refine ⟨858271103935262072250523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4577445887654731052002789 858271103935262072250523)
                      ·
                        rfl

theorem cell23_1671477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1671477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671477 prefixEnd_1671477 := by exact prefixLift 1671477
  have htrace : WordTrace (prefixWord ++ tailWord_1671477) baseStart_1671477 baseEnd_1671477 := by
    simpa [prefixWord, tailWord_1671477, baseEnd_1671477] using wordTrace_append hprefix tailTrace_1671477
  have hstable : (prefixWord ++ tailWord_1671477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671477).length < 2 ^ (prefixWord ++ tailWord_1671477).sum := by decide
  have hdescent : baseEnd_1671477 < baseStart_1671477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671497 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 3]
def baseStart_1671497 : Nat := 118140960795 + 1671497 * 2 ^ 59
def prefixEnd_1671497 : Nat := 4983230072969 + 3 ^ 40 * 1671497 * 2
def baseEnd_1671497 : Nat := 858281373548351994000431

theorem tailTrace_1671497 : CollatzResearch.WordTrace tailWord_1671497 prefixEnd_1671497 858281373548351994000431 := by
  unfold tailWord_1671497
  simp only [CollatzResearch.WordTrace]
  refine ⟨60964504025459312805364745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40643002683639541870243163 60964504025459312805364745)
  ·
    refine ⟨45723378019094484604023559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60964504025459312805364745 45723378019094484604023559)
    ·
      refine ⟨68585067028641726906035339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45723378019094484604023559 68585067028641726906035339)
      ·
        refine ⟨102877600542962590359053009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68585067028641726906035339 102877600542962590359053009)
        ·
          refine ⟨77158200407221942769289757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102877600542962590359053009 77158200407221942769289757)
          ·
            refine ⟨28934325152708228538483659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77158200407221942769289757 28934325152708228538483659)
            ·
              refine ⟨43401487729062342807725489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28934325152708228538483659 43401487729062342807725489)
              ·
                refine ⟨32551115796796757105794117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43401487729062342807725489 32551115796796757105794117)
                ·
                  refine ⟨6103334211899391957336397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32551115796796757105794117 6103334211899391957336397)
                  ·
                    refine ⟨2288750329462271984001149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6103334211899391957336397 2288750329462271984001149)
                    ·
                      refine ⟨858281373548351994000431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2288750329462271984001149 858281373548351994000431)
                      ·
                        rfl

theorem cell23_1671497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_1671497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671497 prefixEnd_1671497 := by exact prefixLift 1671497
  have htrace : WordTrace (prefixWord ++ tailWord_1671497) baseStart_1671497 baseEnd_1671497 := by
    simpa [prefixWord, tailWord_1671497, baseEnd_1671497] using wordTrace_append hprefix tailTrace_1671497
  have hstable : (prefixWord ++ tailWord_1671497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671497).length < 2 ^ (prefixWord ++ tailWord_1671497).sum := by decide
  have hdescent : baseEnd_1671497 < baseStart_1671497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671524 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_1671524 : Nat := 118140960795 + 1671524 * 2 ^ 59
def prefixEnd_1671524 : Nat := 4983230072969 + 3 ^ 40 * 1671524 * 2
def baseEnd_1671524 : Nat := 858295237526023388362807

theorem tailTrace_1671524 : CollatzResearch.WordTrace tailWord_1671524 prefixEnd_1671524 858295237526023388362807 := by
  unfold tailWord_1671524
  simp only [CollatzResearch.WordTrace]
  refine ⟨30482744398180748208298813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40643659197574330944398417 30482744398180748208298813)
  ·
    refine ⟨11431029149317780578112055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30482744398180748208298813 11431029149317780578112055)
    ·
      refine ⟨17146543723976670867168083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11431029149317780578112055 17146543723976670867168083)
      ·
        refine ⟨25719815585965006300752125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17146543723976670867168083 25719815585965006300752125)
        ·
          refine ⟨9644930844736877362782047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25719815585965006300752125 9644930844736877362782047)
          ·
            refine ⟨14467396267105316044173071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9644930844736877362782047 14467396267105316044173071)
            ·
              refine ⟨21701094400657974066259607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14467396267105316044173071 21701094400657974066259607)
              ·
                refine ⟨32551641600986961099389411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21701094400657974066259607 32551641600986961099389411)
                ·
                  refine ⟨48827462401480441649084117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32551641600986961099389411 48827462401480441649084117)
                  ·
                    refine ⟨1144393650034697851150409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48827462401480441649084117 1144393650034697851150409)
                    ·
                      refine ⟨858295237526023388362807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144393650034697851150409 858295237526023388362807)
                      ·
                        rfl

theorem cell23_1671524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_1671524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671524 prefixEnd_1671524 := by exact prefixLift 1671524
  have htrace : WordTrace (prefixWord ++ tailWord_1671524) baseStart_1671524 baseEnd_1671524 := by
    simpa [prefixWord, tailWord_1671524, baseEnd_1671524] using wordTrace_append hprefix tailTrace_1671524
  have hstable : (prefixWord ++ tailWord_1671524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671524).length < 2 ^ (prefixWord ++ tailWord_1671524).sum := by decide
  have hdescent : baseEnd_1671524 < baseStart_1671524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671537 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_1671537 : Nat := 118140960795 + 1671537 * 2 ^ 59
def prefixEnd_1671537 : Nat := 4983230072969 + 3 ^ 40 * 1671537 * 2
def baseEnd_1671537 : Nat := 858301912774531837500247

theorem tailTrace_1671537 : CollatzResearch.WordTrace tailWord_1671537 prefixEnd_1671537 858301912774531837500247 := by
  unfold tailWord_1671537
  simp only [CollatzResearch.WordTrace]
  refine ⟨60965962945314399636820865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40643975296876266424547243 60965962945314399636820865)
  ·
    refine ⟨45724472208985799727615649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60965962945314399636820865 45724472208985799727615649)
    ·
      refine ⟨34293354156739349795711737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45724472208985799727615649 34293354156739349795711737)
      ·
        refine ⟨25720015617554512346783803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34293354156739349795711737 25720015617554512346783803)
        ·
          refine ⟨38580023426331768520175705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25720015617554512346783803 38580023426331768520175705)
          ·
            refine ⟨28935017569748826390131779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38580023426331768520175705 28935017569748826390131779)
            ·
              refine ⟨43402526354623239585197669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28935017569748826390131779 43402526354623239585197669)
              ·
                refine ⟨8137973691491857422224563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43402526354623239585197669 8137973691491857422224563)
                ·
                  refine ⟨12206960537237786133336845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8137973691491857422224563 12206960537237786133336845)
                  ·
                    refine ⟨4577610201464169800001317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12206960537237786133336845 4577610201464169800001317)
                    ·
                      refine ⟨858301912774531837500247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4577610201464169800001317 858301912774531837500247)
                      ·
                        rfl

theorem cell23_1671537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_1671537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671537 prefixEnd_1671537 := by exact prefixLift 1671537
  have htrace : WordTrace (prefixWord ++ tailWord_1671537) baseStart_1671537 baseEnd_1671537 := by
    simpa [prefixWord, tailWord_1671537, baseEnd_1671537] using wordTrace_append hprefix tailTrace_1671537
  have hstable : (prefixWord ++ tailWord_1671537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671537).length < 2 ^ (prefixWord ++ tailWord_1671537).sum := by decide
  have hdescent : baseEnd_1671537 < baseStart_1671537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671577 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 8]
def baseStart_1671577 : Nat := 118140960795 + 1671577 * 2 ^ 59
def prefixEnd_1671577 : Nat := 4983230072969 + 3 ^ 40 * 1671577 * 2
def baseEnd_1671577 : Nat := 95369161333412409000007

theorem tailTrace_1671577 : CollatzResearch.WordTrace tailWord_1671577 prefixEnd_1671577 95369161333412409000007 := by
  unfold tailWord_1671577
  simp only [CollatzResearch.WordTrace]
  refine ⟨60967421865169486468276985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40644947910112990978851323 60967421865169486468276985)
  ·
    refine ⟨45725566398877114851207739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60967421865169486468276985 45725566398877114851207739)
    ·
      refine ⟨68588349598315672276811609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45725566398877114851207739 68588349598315672276811609)
      ·
        refine ⟨51441262198736754207608707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68588349598315672276811609 51441262198736754207608707)
        ·
          refine ⟨77161893298105131311413061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51441262198736754207608707 77161893298105131311413061)
          ·
            refine ⟨14467854993394712120889949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77161893298105131311413061 14467854993394712120889949)
            ·
              refine ⟨5425445622523017045333731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14467854993394712120889949 5425445622523017045333731)
              ·
                refine ⟨8138168433784525568000597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425445622523017045333731 8138168433784525568000597)
                ·
                  refine ⟨95369161333412409000007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8138168433784525568000597 95369161333412409000007)
                  ·
                    rfl

theorem cell23_1671577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 8].length) (baseStart_1671577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671577 prefixEnd_1671577 := by exact prefixLift 1671577
  have htrace : WordTrace (prefixWord ++ tailWord_1671577) baseStart_1671577 baseEnd_1671577 := by
    simpa [prefixWord, tailWord_1671577, baseEnd_1671577] using wordTrace_append hprefix tailTrace_1671577
  have hstable : (prefixWord ++ tailWord_1671577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671577).length < 2 ^ (prefixWord ++ tailWord_1671577).sum := by decide
  have hdescent : baseEnd_1671577 < baseStart_1671577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671658 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_1671658 : Nat := 118140960795 + 1671658 * 2 ^ 59
def prefixEnd_1671658 : Nat := 4983230072969 + 3 ^ 40 * 1671658 * 2
def baseEnd_1671658 : Nat := 286121347977908621362397

theorem tailTrace_1671658 : CollatzResearch.WordTrace tailWord_1671658 prefixEnd_1671658 286121347977908621362397 := by
  unfold tailWord_1671658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15242594044469009325493907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40646917451917358201317085 15242594044469009325493907)
  ·
    refine ⟨22863891066703513988240861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15242594044469009325493907 22863891066703513988240861)
    ·
      refine ⟨8573959150013817745590323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22863891066703513988240861 8573959150013817745590323)
      ·
        refine ⟨12860938725020726618385485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8573959150013817745590323 12860938725020726618385485)
        ·
          refine ⟨4822852021882772481894557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12860938725020726618385485 4822852021882772481894557)
          ·
            refine ⟨1808569508206039680710459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4822852021882772481894557 1808569508206039680710459)
            ·
              refine ⟨2712854262309059521065689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808569508206039680710459 2712854262309059521065689)
              ·
                refine ⟨2034640696731794640799267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712854262309059521065689 2034640696731794640799267)
                ·
                  refine ⟨3051961045097691961198901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034640696731794640799267 3051961045097691961198901)
                  ·
                    refine ⟨286121347977908621362397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3051961045097691961198901 286121347977908621362397)
                    ·
                      rfl

theorem cell23_1671658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_1671658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671658 prefixEnd_1671658 := by exact prefixLift 1671658
  have htrace : WordTrace (prefixWord ++ tailWord_1671658) baseStart_1671658 baseEnd_1671658 := by
    simpa [prefixWord, tailWord_1671658, baseEnd_1671658] using wordTrace_append hprefix tailTrace_1671658
  have hstable : (prefixWord ++ tailWord_1671658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671658).length < 2 ^ (prefixWord ++ tailWord_1671658).sum := by decide
  have hdescent : baseEnd_1671658 < baseStart_1671658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671667 : List Nat := [1, 1, 1, 2, 2, 2, 3, 11]
def baseStart_1671667 : Nat := 118140960795 + 1671667 * 2 ^ 59
def prefixEnd_1671667 : Nat := 4983230072969 + 3 ^ 40 * 1671667 * 2
def baseEnd_1671667 : Nat := 31791432046652456624987

theorem tailTrace_1671667 : CollatzResearch.WordTrace tailWord_1671667 prefixEnd_1671667 31791432046652456624987 := by
  unfold tailWord_1671667
  simp only [CollatzResearch.WordTrace]
  refine ⟨60970704434843431839053255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40647136289895621226035503 60970704434843431839053255)
  ·
    refine ⟨91456056652265147758579883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60970704434843431839053255 91456056652265147758579883)
    ·
      refine ⟨137184084978397721637869825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91456056652265147758579883 137184084978397721637869825)
      ·
        refine ⟨102888063733798291228402369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137184084978397721637869825 102888063733798291228402369)
        ·
          refine ⟨77166047800348718421301777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102888063733798291228402369 77166047800348718421301777)
          ·
            refine ⟨57874535850261538815976333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77166047800348718421301777 57874535850261538815976333)
            ·
              refine ⟨21702950943848077055991125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57874535850261538815976333 21702950943848077055991125)
              ·
                refine ⟨31791432046652456624987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21702950943848077055991125 31791432046652456624987)
                ·
                  rfl

theorem cell23_1671667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 11].length) (baseStart_1671667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671667 prefixEnd_1671667 := by exact prefixLift 1671667
  have htrace : WordTrace (prefixWord ++ tailWord_1671667) baseStart_1671667 baseEnd_1671667 := by
    simpa [prefixWord, tailWord_1671667, baseEnd_1671667] using wordTrace_append hprefix tailTrace_1671667
  have hstable : (prefixWord ++ tailWord_1671667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671667).length < 2 ^ (prefixWord ++ tailWord_1671667).sum := by decide
  have hdescent : baseEnd_1671667 < baseStart_1671667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671681 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1671681 : Nat := 118140960795 + 1671681 * 2 ^ 59
def prefixEnd_1671681 : Nat := 4983230072969 + 3 ^ 40 * 1671681 * 2
def baseEnd_1671681 : Nat := 858375853988779274099585

theorem tailTrace_1671681 : CollatzResearch.WordTrace tailWord_1671681 prefixEnd_1671681 858375853988779274099585 := by
  unfold tailWord_1671681
  simp only [CollatzResearch.WordTrace]
  refine ⟨60971215056792712230062897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40647476704528474820041931 60971215056792712230062897)
  ·
    refine ⟨45728411292594534172547173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60971215056792712230062897 45728411292594534172547173)
    ·
      refine ⟨8574077117361475157352595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45728411292594534172547173 8574077117361475157352595)
      ·
        refine ⟨12861115676042212736028893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8574077117361475157352595 12861115676042212736028893)
        ·
          refine ⟨4822918378515829776010835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12861115676042212736028893 4822918378515829776010835)
          ·
            refine ⟨7234377567773744664016253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822918378515829776010835 7234377567773744664016253)
            ·
              refine ⟨2712891587915154249006095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7234377567773744664016253 2712891587915154249006095)
              ·
                refine ⟨4069337381872731373509143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712891587915154249006095 4069337381872731373509143)
                ·
                  refine ⟨6104006072809097060263715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069337381872731373509143 6104006072809097060263715)
                  ·
                    refine ⟨9156009109213645590395573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6104006072809097060263715 9156009109213645590395573)
                    ·
                      refine ⟨858375853988779274099585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9156009109213645590395573 858375853988779274099585)
                      ·
                        rfl

theorem cell23_1671681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1671681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671681 prefixEnd_1671681 := by exact prefixLift 1671681
  have htrace : WordTrace (prefixWord ++ tailWord_1671681) baseStart_1671681 baseEnd_1671681 := by
    simpa [prefixWord, tailWord_1671681, baseEnd_1671681] using wordTrace_append hprefix tailTrace_1671681
  have hstable : (prefixWord ++ tailWord_1671681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671681).length < 2 ^ (prefixWord ++ tailWord_1671681).sum := by decide
  have hdescent : baseEnd_1671681 < baseStart_1671681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671684 : List Nat := [2, 3, 2, 3, 1, 12]
def baseStart_1671684 : Nat := 118140960795 + 1671684 * 2 ^ 59
def prefixEnd_1671684 : Nat := 4983230072969 + 3 ^ 40 * 1671684 * 2
def baseEnd_1671684 : Nat := 3532417261031863219597

theorem tailTrace_1671684 : CollatzResearch.WordTrace tailWord_1671684 prefixEnd_1671684 3532417261031863219597 := by
  unfold tailWord_1671684
  simp only [CollatzResearch.WordTrace]
  refine ⟨30485662237890921871211053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40647549650521229161614737 30485662237890921871211053)
  ·
    refine ⟨11432123339209095701704145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30485662237890921871211053 11432123339209095701704145)
    ·
      refine ⟨8574092504406821776278109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11432123339209095701704145 8574092504406821776278109)
      ·
        refine ⟨3215284689152558166104291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8574092504406821776278109 3215284689152558166104291)
        ·
          refine ⟨4822927033728837249156437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3215284689152558166104291 4822927033728837249156437)
          ·
            refine ⟨3532417261031863219597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4822927033728837249156437 3532417261031863219597)
            ·
              rfl

theorem cell23_1671684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 12].length) (baseStart_1671684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671684 prefixEnd_1671684 := by exact prefixLift 1671684
  have htrace : WordTrace (prefixWord ++ tailWord_1671684) baseStart_1671684 baseEnd_1671684 := by
    simpa [prefixWord, tailWord_1671684, baseEnd_1671684] using wordTrace_append hprefix tailTrace_1671684
  have hstable : (prefixWord ++ tailWord_1671684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671684).length < 2 ^ (prefixWord ++ tailWord_1671684).sum := by decide
  have hdescent : baseEnd_1671684 < baseStart_1671684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671711 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 3]
def baseStart_1671711 : Nat := 118140960795 + 1671711 * 2 ^ 59
def prefixEnd_1671711 : Nat := 4983230072969 + 3 ^ 40 * 1671711 * 2
def baseEnd_1671711 : Nat := 858391258408414156724447

theorem tailTrace_1671711 : CollatzResearch.WordTrace tailWord_1671711 prefixEnd_1671711 858391258408414156724447 := by
  unfold tailWord_1671711
  simp only [CollatzResearch.WordTrace]
  refine ⟨60972309246684027353654987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40648206164456018235769991 60972309246684027353654987)
  ·
    refine ⟨91458463870026041030482481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60972309246684027353654987 91458463870026041030482481)
    ·
      refine ⟨68593847902519530772861861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91458463870026041030482481 68593847902519530772861861)
      ·
        refine ⟨12861346481722412019911599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68593847902519530772861861 12861346481722412019911599)
        ·
          refine ⟨19292019722583618029867399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12861346481722412019911599 19292019722583618029867399)
          ·
            refine ⟨28938029583875427044801099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19292019722583618029867399 28938029583875427044801099)
            ·
              refine ⟨43407044375813140567201649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28938029583875427044801099 43407044375813140567201649)
              ·
                refine ⟨32555283281859855425401237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43407044375813140567201649 32555283281859855425401237)
                ·
                  refine ⟨1526028903837180723065683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32555283281859855425401237 1526028903837180723065683)
                  ·
                    refine ⟨2289043355755771084598525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1526028903837180723065683 2289043355755771084598525)
                    ·
                      refine ⟨858391258408414156724447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2289043355755771084598525 858391258408414156724447)
                      ·
                        rfl

theorem cell23_1671711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_1671711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671711 prefixEnd_1671711 := by exact prefixLift 1671711
  have htrace : WordTrace (prefixWord ++ tailWord_1671711) baseStart_1671711 baseEnd_1671711 := by
    simpa [prefixWord, tailWord_1671711, baseEnd_1671711] using wordTrace_append hprefix tailTrace_1671711
  have hstable : (prefixWord ++ tailWord_1671711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671711).length < 2 ^ (prefixWord ++ tailWord_1671711).sum := by decide
  have hdescent : baseEnd_1671711 < baseStart_1671711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671714 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1671714 : Nat := 118140960795 + 1671714 * 2 ^ 59
def prefixEnd_1671714 : Nat := 4983230072969 + 3 ^ 40 * 1671714 * 2
def baseEnd_1671714 : Nat := 286130932950125881662311

theorem tailTrace_1671714 : CollatzResearch.WordTrace tailWord_1671714 prefixEnd_1671714 286130932950125881662311 := by
  unfold tailWord_1671714
  simp only [CollatzResearch.WordTrace]
  refine ⟨15243104666418289716503549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40648279110448772577342797 15243104666418289716503549)
  ·
    refine ⟨5716164249906858643688831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15243104666418289716503549 5716164249906858643688831)
    ·
      refine ⟨8574246374860287965533247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5716164249906858643688831 8574246374860287965533247)
      ·
        refine ⟨12861369562290431948299871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8574246374860287965533247 12861369562290431948299871)
        ·
          refine ⟨19292054343435647922449807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12861369562290431948299871 19292054343435647922449807)
          ·
            refine ⟨28938081515153471883674711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19292054343435647922449807 28938081515153471883674711)
            ·
              refine ⟨43407122272730207825512067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28938081515153471883674711 43407122272730207825512067)
              ·
                refine ⟨65110683409095311738268101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43407122272730207825512067 65110683409095311738268101)
                ·
                  refine ⟨12208253139205370950925269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65110683409095311738268101 12208253139205370950925269)
                  ·
                    refine ⟨286130932950125881662311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12208253139205370950925269 286130932950125881662311)
                    ·
                      rfl

theorem cell23_1671714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1671714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671714 prefixEnd_1671714 := by exact prefixLift 1671714
  have htrace : WordTrace (prefixWord ++ tailWord_1671714) baseStart_1671714 baseEnd_1671714 := by
    simpa [prefixWord, tailWord_1671714, baseEnd_1671714] using wordTrace_append hprefix tailTrace_1671714
  have hstable : (prefixWord ++ tailWord_1671714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671714).length < 2 ^ (prefixWord ++ tailWord_1671714).sum := by decide
  have hdescent : baseEnd_1671714 < baseStart_1671714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671732 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1671732 : Nat := 118140960795 + 1671732 * 2 ^ 59
def prefixEnd_1671732 : Nat := 4983230072969 + 3 ^ 40 * 1671732 * 2
def baseEnd_1671732 : Nat := 858402041502158574561851

theorem tailTrace_1671732 : CollatzResearch.WordTrace tailWord_1671732 prefixEnd_1671732 858402041502158574561851 := by
  unfold tailWord_1671732
  simp only [CollatzResearch.WordTrace]
  refine ⟨30486537589803973970084725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40648716786405298626779633 30486537589803973970084725)
  ·
    refine ⟨2858112899044122559695443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30486537589803973970084725 2858112899044122559695443)
    ·
      refine ⟨4287169348566183839543165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2858112899044122559695443 4287169348566183839543165)
      ·
        refine ⟨1607688505712318939828687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4287169348566183839543165 1607688505712318939828687)
        ·
          refine ⟨2411532758568478409743031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607688505712318939828687 2411532758568478409743031)
          ·
            refine ⟨3617299137852717614614547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411532758568478409743031 3617299137852717614614547)
            ·
              refine ⟨5425948706779076421921821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617299137852717614614547 5425948706779076421921821)
              ·
                refine ⟨2034730765042153658220683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5425948706779076421921821 2034730765042153658220683)
                ·
                  refine ⟨3052096147563230487331025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034730765042153658220683 3052096147563230487331025)
                  ·
                    refine ⟨2289072110672422865498269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3052096147563230487331025 2289072110672422865498269)
                    ·
                      refine ⟨858402041502158574561851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2289072110672422865498269 858402041502158574561851)
                      ·
                        rfl

theorem cell23_1671732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1671732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671732 prefixEnd_1671732 := by exact prefixLift 1671732
  have htrace : WordTrace (prefixWord ++ tailWord_1671732) baseStart_1671732 baseEnd_1671732 := by
    simpa [prefixWord, tailWord_1671732, baseEnd_1671732] using wordTrace_append hprefix tailTrace_1671732
  have hstable : (prefixWord ++ tailWord_1671732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671732).length < 2 ^ (prefixWord ++ tailWord_1671732).sum := by decide
  have hdescent : baseEnd_1671732 < baseStart_1671732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671744 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 2, 6]
def baseStart_1671744 : Nat := 118140960795 + 1671744 * 2 ^ 59
def prefixEnd_1671744 : Nat := 4983230072969 + 3 ^ 40 * 1671744 * 2
def baseEnd_1671744 : Nat := 286136067756670842537265

theorem tailTrace_1671744 : CollatzResearch.WordTrace tailWord_1671744 prefixEnd_1671744 286136067756670842537265 := by
  unfold tailWord_1671744
  simp only [CollatzResearch.WordTrace]
  refine ⟨30486756427782236994803143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40649008570376315993070857 30486756427782236994803143)
  ·
    refine ⟨45730134641673355492204715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30486756427782236994803143 45730134641673355492204715)
    ·
      refine ⟨68595201962510033238307073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45730134641673355492204715 68595201962510033238307073)
      ·
        refine ⟨51446401471882524928730305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68595201962510033238307073 51446401471882524928730305)
        ·
          refine ⟨38584801103911893696547729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51446401471882524928730305 38584801103911893696547729)
          ·
            refine ⟨28938600827933920272410797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38584801103911893696547729 28938600827933920272410797)
            ·
              refine ⟨10851975310475220102154049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28938600827933920272410797 10851975310475220102154049)
              ·
                refine ⟨8138981482856415076615537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10851975310475220102154049 8138981482856415076615537)
                ·
                  refine ⟨6104236112142311307461653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8138981482856415076615537 6104236112142311307461653)
                  ·
                    refine ⟨286136067756670842537265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6104236112142311307461653 286136067756670842537265)
                    ·
                      rfl

theorem cell23_1671744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_1671744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671744 prefixEnd_1671744 := by exact prefixLift 1671744
  have htrace : WordTrace (prefixWord ++ tailWord_1671744) baseStart_1671744 baseEnd_1671744 := by
    simpa [prefixWord, tailWord_1671744, baseEnd_1671744] using wordTrace_append hprefix tailTrace_1671744
  have hstable : (prefixWord ++ tailWord_1671744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671744).length < 2 ^ (prefixWord ++ tailWord_1671744).sum := by decide
  have hdescent : baseEnd_1671744 < baseStart_1671744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671745 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1671745 : Nat := 118140960795 + 1671745 * 2 ^ 59
def prefixEnd_1671745 : Nat := 4983230072969 + 3 ^ 40 * 1671745 * 2
def baseEnd_1671745 : Nat := 858408716750667023699291

theorem tailTrace_1671745 : CollatzResearch.WordTrace tailWord_1671745 prefixEnd_1671745 858408716750667023699291 := by
  unfold tailWord_1671745
  simp only [CollatzResearch.WordTrace]
  refine ⟨60973549328560851160392689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40649032885707234106928459 60973549328560851160392689)
  ·
    refine ⟨45730161996420638370294517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60973549328560851160392689 45730161996420638370294517)
    ·
      refine ⟨4287202687164434847215111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45730161996420638370294517 4287202687164434847215111)
      ·
        refine ⟨6430804030746652270822667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287202687164434847215111 6430804030746652270822667)
        ·
          refine ⟨9646206046119978406234001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6430804030746652270822667 9646206046119978406234001)
          ·
            refine ⟨7234654534589983804675501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9646206046119978406234001 7234654534589983804675501)
            ·
              refine ⟨2712995450471243926753313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7234654534589983804675501 2712995450471243926753313)
              ·
                refine ⟨2034746587853432945064985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712995450471243926753313 2034746587853432945064985)
                ·
                  refine ⟨1526059940890074708798739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2034746587853432945064985 1526059940890074708798739)
                  ·
                    refine ⟨2289089911335112063198109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1526059940890074708798739 2289089911335112063198109)
                    ·
                      refine ⟨858408716750667023699291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2289089911335112063198109 858408716750667023699291)
                      ·
                        rfl

theorem cell23_1671745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1671745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671745 prefixEnd_1671745 := by exact prefixLift 1671745
  have htrace : WordTrace (prefixWord ++ tailWord_1671745) baseStart_1671745 baseEnd_1671745 := by
    simpa [prefixWord, tailWord_1671745, baseEnd_1671745] using wordTrace_append hprefix tailTrace_1671745
  have hstable : (prefixWord ++ tailWord_1671745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671745).length < 2 ^ (prefixWord ++ tailWord_1671745).sum := by decide
  have hdescent : baseEnd_1671745 < baseStart_1671745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671768 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 1, 4, 2]
def baseStart_1671768 : Nat := 118140960795 + 1671768 * 2 ^ 59
def prefixEnd_1671768 : Nat := 4983230072969 + 3 ^ 40 * 1671768 * 2
def baseEnd_1671768 : Nat := 858420526805720433711685

theorem tailTrace_1671768 : CollatzResearch.WordTrace tailWord_1671768 prefixEnd_1671768 858420526805720433711685 := by
  unfold tailWord_1671768
  simp only [CollatzResearch.WordTrace]
  refine ⟨30487194103738763044239979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40649592138318350725653305 30487194103738763044239979)
  ·
    refine ⟨45730791155608144566359969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30487194103738763044239979 45730791155608144566359969)
    ·
      refine ⟨34298093366706108424769977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45730791155608144566359969 34298093366706108424769977)
      ·
        refine ⟨25723570025029581318577483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34298093366706108424769977 25723570025029581318577483)
        ·
          refine ⟨38585355037544371977866225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25723570025029581318577483 38585355037544371977866225)
          ·
            refine ⟨28939016278158278983399669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38585355037544371977866225 28939016278158278983399669)
            ·
              refine ⟨2713032776077338654693719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28939016278158278983399669 2713032776077338654693719)
              ·
                refine ⟨4069549164116007982040579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713032776077338654693719 4069549164116007982040579)
                ·
                  refine ⟨6104323746174011973060869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069549164116007982040579 6104323746174011973060869)
                  ·
                    refine ⟨1144560702407627244948913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6104323746174011973060869 1144560702407627244948913)
                    ·
                      refine ⟨858420526805720433711685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144560702407627244948913 858420526805720433711685)
                      ·
                        rfl

theorem cell23_1671768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_1671768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671768 prefixEnd_1671768 := by exact prefixLift 1671768
  have htrace : WordTrace (prefixWord ++ tailWord_1671768) baseStart_1671768 baseEnd_1671768 := by
    simpa [prefixWord, tailWord_1671768, baseEnd_1671768] using wordTrace_append hprefix tailTrace_1671768
  have hstable : (prefixWord ++ tailWord_1671768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671768).length < 2 ^ (prefixWord ++ tailWord_1671768).sum := by decide
  have hdescent : baseEnd_1671768 < baseStart_1671768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671772 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_1671772 : Nat := 118140960795 + 1671772 * 2 ^ 59
def prefixEnd_1671772 : Nat := 4983230072969 + 3 ^ 40 * 1671772 * 2
def baseEnd_1671772 : Nat := 858422580728338418061667

theorem tailTrace_1671772 : CollatzResearch.WordTrace tailWord_1671772 prefixEnd_1671772 858422580728338418061667 := by
  unfold tailWord_1671772
  simp only [CollatzResearch.WordTrace]
  refine ⟨30487267049731517385812785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40649689399642023181083713 30487267049731517385812785)
  ·
    refine ⟨22865450287298638039359589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30487267049731517385812785 22865450287298638039359589)
    ·
      refine ⟨4287271928868494632379923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22865450287298638039359589 4287271928868494632379923)
      ·
        refine ⟨6430907893302741948569885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287271928868494632379923 6430907893302741948569885)
        ·
          refine ⟨2411590459988528230713707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6430907893302741948569885 2411590459988528230713707)
          ·
            refine ⟨3617385689982792346070561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411590459988528230713707 3617385689982792346070561)
            ·
              refine ⟨2713039267487094259552921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3617385689982792346070561 2713039267487094259552921)
              ·
                refine ⟨2034779450615320694664691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2713039267487094259552921 2034779450615320694664691)
                ·
                  refine ⟨3052169175922981041997037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034779450615320694664691 3052169175922981041997037)
                  ·
                    refine ⟨1144563440971117890748889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3052169175922981041997037 1144563440971117890748889)
                    ·
                      refine ⟨858422580728338418061667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144563440971117890748889 858422580728338418061667)
                      ·
                        rfl

theorem cell23_1671772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_1671772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671772 prefixEnd_1671772 := by exact prefixLift 1671772
  have htrace : WordTrace (prefixWord ++ tailWord_1671772) baseStart_1671772 baseEnd_1671772 := by
    simpa [prefixWord, tailWord_1671772, baseEnd_1671772] using wordTrace_append hprefix tailTrace_1671772
  have hstable : (prefixWord ++ tailWord_1671772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671772).length < 2 ^ (prefixWord ++ tailWord_1671772).sum := by decide
  have hdescent : baseEnd_1671772 < baseStart_1671772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671858 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_1671858 : Nat := 118140960795 + 1671858 * 2 ^ 59
def prefixEnd_1671858 : Nat := 4983230072969 + 3 ^ 40 * 1671858 * 2
def baseEnd_1671858 : Nat := 858466740064625081586271

theorem tailTrace_1671858 : CollatzResearch.WordTrace tailWord_1671858 prefixEnd_1671858 858466740064625081586271 := by
  unfold tailWord_1671858
  simp only [CollatzResearch.WordTrace]
  refine ⟨15244417694287867864814057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40651780518100980972837485 15244417694287867864814057)
  ·
    refine ⟨11433313270715900898610543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15244417694287867864814057 11433313270715900898610543)
    ·
      refine ⟨17149969906073851347915815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11433313270715900898610543 17149969906073851347915815)
      ·
        refine ⟨25724954859110777021873723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17149969906073851347915815 25724954859110777021873723)
        ·
          refine ⟨38587432288666165532810585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25724954859110777021873723 38587432288666165532810585)
          ·
            refine ⟨28940574216499624149607939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38587432288666165532810585 28940574216499624149607939)
            ·
              refine ⟨43410861324749436224411909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28940574216499624149607939 43410861324749436224411909)
              ·
                refine ⟨8139536498390519292077233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43410861324749436224411909 8139536498390519292077233)
                ·
                  refine ⟨6104652373792889469057925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8139536498390519292077233 6104652373792889469057925)
                  ·
                    refine ⟨1144622320086166775448361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6104652373792889469057925 1144622320086166775448361)
                    ·
                      refine ⟨858466740064625081586271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144622320086166775448361 858466740064625081586271)
                      ·
                        rfl

theorem cell23_1671858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_1671858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671858 prefixEnd_1671858 := by exact prefixLift 1671858
  have htrace : WordTrace (prefixWord ++ tailWord_1671858) baseStart_1671858 baseEnd_1671858 := by
    simpa [prefixWord, tailWord_1671858, baseEnd_1671858] using wordTrace_append hprefix tailTrace_1671858
  have hstable : (prefixWord ++ tailWord_1671858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671858).length < 2 ^ (prefixWord ++ tailWord_1671858).sum := by decide
  have hdescent : baseEnd_1671858 < baseStart_1671858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671868 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_1671868 : Nat := 118140960795 + 1671868 * 2 ^ 59
def prefixEnd_1671868 : Nat := 4983230072969 + 3 ^ 40 * 1671868 * 2
def baseEnd_1671868 : Nat := 286157291623723347487075

theorem tailTrace_1671868 : CollatzResearch.WordTrace tailWord_1671868 prefixEnd_1671868 286157291623723347487075 := by
  unfold tailWord_1671868
  simp only [CollatzResearch.WordTrace]
  refine ⟨30489017753557621583560129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40652023671410162111413505 30489017753557621583560129)
  ·
    refine ⟨22866763315168216187670097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30489017753557621583560129 22866763315168216187670097)
    ·
      refine ⟨17150072486376162140752573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22866763315168216187670097 17150072486376162140752573)
      ·
        refine ⟨6431277182391060802782215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17150072486376162140752573 6431277182391060802782215)
        ·
          refine ⟨9646915773586591204173323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6431277182391060802782215 9646915773586591204173323)
          ·
            refine ⟨14470373660379886806259985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9646915773586591204173323 14470373660379886806259985)
            ·
              refine ⟨10852780245284915104694989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14470373660379886806259985 10852780245284915104694989)
              ·
                refine ⟨4069792591981843164260621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10852780245284915104694989 4069792591981843164260621)
                ·
                  refine ⟨1526172221993191186597733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4069792591981843164260621 1526172221993191186597733)
                  ·
                    refine ⟨286157291623723347487075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1526172221993191186597733 286157291623723347487075)
                    ·
                      rfl

theorem cell23_1671868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_1671868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671868 prefixEnd_1671868 := by exact prefixLift 1671868
  have htrace : WordTrace (prefixWord ++ tailWord_1671868) baseStart_1671868 baseEnd_1671868 := by
    simpa [prefixWord, tailWord_1671868, baseEnd_1671868] using wordTrace_append hprefix tailTrace_1671868
  have hstable : (prefixWord ++ tailWord_1671868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671868).length < 2 ^ (prefixWord ++ tailWord_1671868).sum := by decide
  have hdescent : baseEnd_1671868 < baseStart_1671868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671892 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1671892 : Nat := 118140960795 + 1671892 * 2 ^ 59
def prefixEnd_1671892 : Nat := 4983230072969 + 3 ^ 40 * 1671892 * 2
def baseEnd_1671892 : Nat := 858484198406877948561115

theorem tailTrace_1671892 : CollatzResearch.WordTrace tailWord_1671892 prefixEnd_1671892 858484198406877948561115 := by
  unfold tailWord_1671892
  simp only [CollatzResearch.WordTrace]
  refine ⟨30489455429514147632996965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40652607239352196843995953 30489455429514147632996965)
  ·
    refine ⟨5716772893033902681186931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30489455429514147632996965 5716772893033902681186931)
    ·
      refine ⟨8575159339550854021780397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5716772893033902681186931 8575159339550854021780397)
      ·
        refine ⟨3215684752331570258167649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8575159339550854021780397 3215684752331570258167649)
        ·
          refine ⟨2411763564248677693625737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3215684752331570258167649 2411763564248677693625737)
          ·
            refine ⟨1808822673186508270219303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2411763564248677693625737 1808822673186508270219303)
            ·
              refine ⟨2713234009779762405328955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808822673186508270219303 2713234009779762405328955)
              ·
                refine ⟨4069851014669643607993433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713234009779762405328955 4069851014669643607993433)
                ·
                  refine ⟨3052388261002232705995075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4069851014669643607993433 3052388261002232705995075)
                  ·
                    refine ⟨4578582391503349058992613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3052388261002232705995075 4578582391503349058992613)
                    ·
                      refine ⟨858484198406877948561115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4578582391503349058992613 858484198406877948561115)
                      ·
                        rfl

theorem cell23_1671892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1671892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671892 prefixEnd_1671892 := by exact prefixLift 1671892
  have htrace : WordTrace (prefixWord ++ tailWord_1671892) baseStart_1671892 baseEnd_1671892 := by
    simpa [prefixWord, tailWord_1671892, baseEnd_1671892] using wordTrace_append hprefix tailTrace_1671892
  have hstable : (prefixWord ++ tailWord_1671892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671892).length < 2 ^ (prefixWord ++ tailWord_1671892).sum := by decide
  have hdescent : baseEnd_1671892 < baseStart_1671892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671895 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 3]
def baseStart_1671895 : Nat := 118140960795 + 1671895 * 2 ^ 59
def prefixEnd_1671895 : Nat := 4983230072969 + 3 ^ 40 * 1671895 * 2
def baseEnd_1671895 : Nat := 858485738848841436823601

theorem tailTrace_1671895 : CollatzResearch.WordTrace tailWord_1671895 prefixEnd_1671895 858485738848841436823601 := by
  unfold tailWord_1671895
  simp only [CollatzResearch.WordTrace]
  refine ⟨60979020278017426778353139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40652680185344951185568759 60979020278017426778353139)
  ·
    refine ⟨91468530417026140167529709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60979020278017426778353139 91468530417026140167529709)
    ·
      refine ⟨34300698906384802562823641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91468530417026140167529709 34300698906384802562823641)
      ·
        refine ⟨25725524179788601922117731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34300698906384802562823641 25725524179788601922117731)
        ·
          refine ⟨38588286269682902883176597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25725524179788601922117731 38588286269682902883176597)
          ·
            refine ⟨1808825918891386072648903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38588286269682902883176597 1808825918891386072648903)
            ·
              refine ⟨2713238878337079108973355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808825918891386072648903 2713238878337079108973355)
              ·
                refine ⟨4069858317505618663460033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713238878337079108973355 4069858317505618663460033)
                ·
                  refine ⟨3052393738129213997595025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4069858317505618663460033 3052393738129213997595025)
                  ·
                    refine ⟨2289295303596910498196269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3052393738129213997595025 2289295303596910498196269)
                    ·
                      refine ⟨858485738848841436823601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2289295303596910498196269 858485738848841436823601)
                      ·
                        rfl

theorem cell23_1671895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_1671895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671895 prefixEnd_1671895 := by exact prefixLift 1671895
  have htrace : WordTrace (prefixWord ++ tailWord_1671895) baseStart_1671895 baseEnd_1671895 := by
    simpa [prefixWord, tailWord_1671895, baseEnd_1671895] using wordTrace_append hprefix tailTrace_1671895
  have hstable : (prefixWord ++ tailWord_1671895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671895).length < 2 ^ (prefixWord ++ tailWord_1671895).sum := by decide
  have hdescent : baseEnd_1671895 < baseStart_1671895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671948 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 1, 8, 2]
def baseStart_1671948 : Nat := 118140960795 + 1671948 * 2 ^ 59
def prefixEnd_1671948 : Nat := 4983230072969 + 3 ^ 40 * 1671948 * 2
def baseEnd_1671948 : Nat := 858512953323529729460857

theorem tailTrace_1671948 : CollatzResearch.WordTrace tailWord_1671948 prefixEnd_1671948 858512953323529729460857 := by
  unfold tailWord_1671948
  simp only [CollatzResearch.WordTrace]
  refine ⟨30490476673412708415016249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40653968897883611220021665 30490476673412708415016249)
  ·
    refine ⟨22867857505059531311262187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30490476673412708415016249 22867857505059531311262187)
    ·
      refine ⟨34301786257589296966893281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22867857505059531311262187 34301786257589296966893281)
      ·
        refine ⟨25726339693191972725169961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34301786257589296966893281 25726339693191972725169961)
        ·
          refine ⟨19294754769893979543877471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25726339693191972725169961 19294754769893979543877471)
          ·
            refine ⟨28942132154840969315816207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19294754769893979543877471 28942132154840969315816207)
            ·
              refine ⟨43413198232261453973724311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28942132154840969315816207 43413198232261453973724311)
              ·
                refine ⟨65119797348392180960586467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43413198232261453973724311 65119797348392180960586467)
                ·
                  refine ⟨97679696022588271440879701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65119797348392180960586467 97679696022588271440879701)
                  ·
                    refine ⟨1144683937764706305947809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97679696022588271440879701 1144683937764706305947809)
                    ·
                      refine ⟨858512953323529729460857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144683937764706305947809 858512953323529729460857)
                      ·
                        rfl

theorem cell23_1671948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_1671948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671948 prefixEnd_1671948 := by exact prefixLift 1671948
  have htrace : WordTrace (prefixWord ++ tailWord_1671948) baseStart_1671948 baseEnd_1671948 := by
    simpa [prefixWord, tailWord_1671948, baseEnd_1671948] using wordTrace_append hprefix tailTrace_1671948
  have hstable : (prefixWord ++ tailWord_1671948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671948).length < 2 ^ (prefixWord ++ tailWord_1671948).sum := by decide
  have hdescent : baseEnd_1671948 < baseStart_1671948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671951 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_1671951 : Nat := 118140960795 + 1671951 * 2 ^ 59
def prefixEnd_1671951 : Nat := 4983230072969 + 3 ^ 40 * 1671951 * 2
def baseEnd_1671951 : Nat := 858514493765493217723343

theorem tailTrace_1671951 : CollatzResearch.WordTrace tailWord_1671951 prefixEnd_1671951 858514493765493217723343 := by
  unfold tailWord_1671951
  simp only [CollatzResearch.WordTrace]
  refine ⟨60981062765814548342391707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40654041843876365561594471 60981062765814548342391707)
  ·
    refine ⟨91471594148721822513587561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60981062765814548342391707 91471594148721822513587561)
    ·
      refine ⟨68603695611541366885190671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91471594148721822513587561 68603695611541366885190671)
      ·
        refine ⟨102905543417312050327786007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68603695611541366885190671 102905543417312050327786007)
        ·
          refine ⟨154358315125968075491679011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102905543417312050327786007 154358315125968075491679011)
          ·
            refine ⟨231537472688952113237518517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154358315125968075491679011 231537472688952113237518517)
            ·
              refine ⟨21706638064589260616017361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231537472688952113237518517 21706638064589260616017361)
              ·
                refine ⟨16279978548441945462013021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21706638064589260616017361 16279978548441945462013021)
                ·
                  refine ⟨6104991955665729548254883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16279978548441945462013021 6104991955665729548254883)
                  ·
                    refine ⟨9157487933498594322382325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6104991955665729548254883 9157487933498594322382325)
                    ·
                      refine ⟨858514493765493217723343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9157487933498594322382325 858514493765493217723343)
                      ·
                        rfl

theorem cell23_1671951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_1671951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671951 prefixEnd_1671951 := by exact prefixLift 1671951
  have htrace : WordTrace (prefixWord ++ tailWord_1671951) baseStart_1671951 baseEnd_1671951 := by
    simpa [prefixWord, tailWord_1671951, baseEnd_1671951] using wordTrace_append hprefix tailTrace_1671951
  have hstable : (prefixWord ++ tailWord_1671951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671951).length < 2 ^ (prefixWord ++ tailWord_1671951).sum := by decide
  have hdescent : baseEnd_1671951 < baseStart_1671951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671968 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1671968 : Nat := 118140960795 + 1671968 * 2 ^ 59
def prefixEnd_1671968 : Nat := 4983230072969 + 3 ^ 40 * 1671968 * 2
def baseEnd_1671968 : Nat := 858523222936619651210765

theorem tailTrace_1671968 : CollatzResearch.WordTrace tailWord_1671968 prefixEnd_1671968 858523222936619651210765 := by
  unfold tailWord_1671968
  simp only [CollatzResearch.WordTrace]
  refine ⟨30490841403376480122880279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40654455204501973497173705 30490841403376480122880279)
  ·
    refine ⟨45736262105064720184320419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30490841403376480122880279 45736262105064720184320419)
    ·
      refine ⟨68604393157597080276480629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45736262105064720184320419 68604393157597080276480629)
      ·
        refine ⟨6431661858524726275920059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68604393157597080276480629 6431661858524726275920059)
        ·
          refine ⟨9647492787787089413880089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6431661858524726275920059 9647492787787089413880089)
          ·
            refine ⟨7235619590840317060410067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9647492787787089413880089 7235619590840317060410067)
            ·
              refine ⟨10853429386260475590615101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7235619590840317060410067 10853429386260475590615101)
              ·
                refine ⟨4070036019847678346480663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10853429386260475590615101 4070036019847678346480663)
                ·
                  refine ⟨6105054029771517519720995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070036019847678346480663 6105054029771517519720995)
                  ·
                    refine ⟨9157581044657276279581493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6105054029771517519720995 9157581044657276279581493)
                    ·
                      refine ⟨858523222936619651210765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9157581044657276279581493 858523222936619651210765)
                      ·
                        rfl

theorem cell23_1671968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1671968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671968 prefixEnd_1671968 := by exact prefixLift 1671968
  have htrace : WordTrace (prefixWord ++ tailWord_1671968) baseStart_1671968 baseEnd_1671968 := by
    simpa [prefixWord, tailWord_1671968, baseEnd_1671968] using wordTrace_append hprefix tailTrace_1671968
  have hstable : (prefixWord ++ tailWord_1671968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671968).length < 2 ^ (prefixWord ++ tailWord_1671968).sum := by decide
  have hdescent : baseEnd_1671968 < baseStart_1671968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671991 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_1671991 : Nat := 118140960795 + 1671991 * 2 ^ 59
def prefixEnd_1671991 : Nat := 4983230072969 + 3 ^ 40 * 1671991 * 2
def baseEnd_1671991 : Nat := 858535032991673061223159

theorem tailTrace_1671991 : CollatzResearch.WordTrace tailWord_1671991 prefixEnd_1671991 858535032991673061223159 := by
  unfold tailWord_1671991
  simp only [CollatzResearch.WordTrace]
  refine ⟨60982521685669635173847827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40655014457113090115898551 60982521685669635173847827)
  ·
    refine ⟨91473782528504452760771741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60982521685669635173847827 91473782528504452760771741)
    ·
      refine ⟨34302668448189169785289403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91473782528504452760771741 34302668448189169785289403)
      ·
        refine ⟨51454002672283754677934105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34302668448189169785289403 51454002672283754677934105)
        ·
          refine ⟨38590502004212816008450579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51454002672283754677934105 38590502004212816008450579)
          ·
            refine ⟨57885753006319224012675869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38590502004212816008450579 57885753006319224012675869)
            ·
              refine ⟨21707157377369709004753451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57885753006319224012675869 21707157377369709004753451)
              ·
                refine ⟨32560736066054563507130177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21707157377369709004753451 32560736066054563507130177)
                ·
                  refine ⟨24420552049540922630347633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32560736066054563507130177 24420552049540922630347633)
                  ·
                    refine ⟨18315414037155691972760725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24420552049540922630347633 18315414037155691972760725)
                    ·
                      refine ⟨858535032991673061223159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18315414037155691972760725 858535032991673061223159)
                      ·
                        rfl

theorem cell23_1671991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_1671991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1671991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1671991 prefixEnd_1671991 := by exact prefixLift 1671991
  have htrace : WordTrace (prefixWord ++ tailWord_1671991) baseStart_1671991 baseEnd_1671991 := by
    simpa [prefixWord, tailWord_1671991, baseEnd_1671991] using wordTrace_append hprefix tailTrace_1671991
  have hstable : (prefixWord ++ tailWord_1671991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671991).length < 2 ^ (prefixWord ++ tailWord_1671991).sum := by decide
  have hdescent : baseEnd_1671991 < baseStart_1671991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672032 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 2, 1, 3]
def baseStart_1672032 : Nat := 118140960795 + 1672032 * 2 ^ 59
def prefixEnd_1672032 : Nat := 4983230072969 + 3 ^ 40 * 1672032 * 2
def baseEnd_1672032 : Nat := 858556085698507400810471

theorem tailTrace_1672032 : CollatzResearch.WordTrace tailWord_1672032 prefixEnd_1672032 858556085698507400810471 := by
  unfold tailWord_1672032
  simp only [CollatzResearch.WordTrace]
  refine ⟨30492008539260549588045175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40656011385680732784060233 30492008539260549588045175)
  ·
    refine ⟨45738012808890824382067763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30492008539260549588045175 45738012808890824382067763)
    ·
      refine ⟨68607019213336236573101645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45738012808890824382067763 68607019213336236573101645)
      ·
        refine ⟨25727632205001088714913117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68607019213336236573101645 25727632205001088714913117)
        ·
          refine ⟨9647862076875408268092419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25727632205001088714913117 9647862076875408268092419)
          ·
            refine ⟨14471793115313112402138629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9647862076875408268092419 14471793115313112402138629)
            ·
              refine ⟨2713461209121208575400993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14471793115313112402138629 2713461209121208575400993)
              ·
                refine ⟨2035095906840906431550745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2713461209121208575400993 2035095906840906431550745)
                ·
                  refine ⟨1526321930130679823663059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2035095906840906431550745 1526321930130679823663059)
                  ·
                    refine ⟨2289482895196019735494589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1526321930130679823663059 2289482895196019735494589)
                    ·
                      refine ⟨858556085698507400810471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2289482895196019735494589 858556085698507400810471)
                      ·
                        rfl

theorem cell23_1672032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_1672032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672032 prefixEnd_1672032 := by exact prefixLift 1672032
  have htrace : WordTrace (prefixWord ++ tailWord_1672032) baseStart_1672032 baseEnd_1672032 := by
    simpa [prefixWord, tailWord_1672032, baseEnd_1672032] using wordTrace_append hprefix tailTrace_1672032
  have hstable : (prefixWord ++ tailWord_1672032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672032).length < 2 ^ (prefixWord ++ tailWord_1672032).sum := by decide
  have hdescent : baseEnd_1672032 < baseStart_1672032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672058 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_1672058 : Nat := 118140960795 + 1672058 * 2 ^ 59
def prefixEnd_1672058 : Nat := 4983230072969 + 3 ^ 40 * 1672058 * 2
def baseEnd_1672058 : Nat := 858569436195524299085351

theorem tailTrace_1672058 : CollatzResearch.WordTrace tailWord_1672058 prefixEnd_1672058 858569436195524299085351 := by
  unfold tailWord_1672058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15246241344106726404134207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40656643584284603744357885 15246241344106726404134207)
  ·
    refine ⟨22869362016160089606201311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15246241344106726404134207 22869362016160089606201311)
    ·
      refine ⟨34304043024240134409301967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22869362016160089606201311 34304043024240134409301967)
      ·
        refine ⟨51456064536360201613952951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34304043024240134409301967 51456064536360201613952951)
        ·
          refine ⟨77184096804540302420929427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51456064536360201613952951 77184096804540302420929427)
          ·
            refine ⟨115776145206810453631394141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77184096804540302420929427 115776145206810453631394141)
            ·
              refine ⟨43416054452553920111772803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115776145206810453631394141 43416054452553920111772803)
              ·
                refine ⟨65124081678830880167659205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43416054452553920111772803 65124081678830880167659205)
                ·
                  refine ⟨12210765314780790031436101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65124081678830880167659205 12210765314780790031436101)
                  ·
                    refine ⟨2289518496521398130894269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12210765314780790031436101 2289518496521398130894269)
                    ·
                      refine ⟨858569436195524299085351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2289518496521398130894269 858569436195524299085351)
                      ·
                        rfl

theorem cell23_1672058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_1672058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672058 prefixEnd_1672058 := by exact prefixLift 1672058
  have htrace : WordTrace (prefixWord ++ tailWord_1672058) baseStart_1672058 baseEnd_1672058 := by
    simpa [prefixWord, tailWord_1672058, baseEnd_1672058] using wordTrace_append hprefix tailTrace_1672058
  have hstable : (prefixWord ++ tailWord_1672058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672058).length < 2 ^ (prefixWord ++ tailWord_1672058).sum := by decide
  have hdescent : baseEnd_1672058 < baseStart_1672058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672068 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1672068 : Nat := 118140960795 + 1672068 * 2 ^ 59
def prefixEnd_1672068 : Nat := 4983230072969 + 3 ^ 40 * 1672068 * 2
def baseEnd_1672068 : Nat := 858574571002069259960305

theorem tailTrace_1672068 : CollatzResearch.WordTrace tailWord_1672068 prefixEnd_1672068 858574571002069259960305 := by
  unfold tailWord_1672068
  simp only [CollatzResearch.WordTrace]
  refine ⟨30492665053195338662200429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40656886737593784882933905 30492665053195338662200429)
  ·
    refine ⟨11434749394948251998325161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30492665053195338662200429 11434749394948251998325161)
    ·
      refine ⟨8576062046211188998743871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11434749394948251998325161 8576062046211188998743871)
      ·
        refine ⟨12864093069316783498115807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8576062046211188998743871 12864093069316783498115807)
        ·
          refine ⟨19296139603975175247173711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12864093069316783498115807 19296139603975175247173711)
          ·
            refine ⟨28944209405962762870760567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19296139603975175247173711 28944209405962762870760567)
            ·
              refine ⟨43416314108944144306140851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28944209405962762870760567 43416314108944144306140851)
              ·
                refine ⟨65124471163416216459211277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43416314108944144306140851 65124471163416216459211277)
                ·
                  refine ⟨24421676686281081172204229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65124471163416216459211277 24421676686281081172204229)
                  ·
                    refine ⟨4579064378677702719788293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24421676686281081172204229 4579064378677702719788293)
                    ·
                      refine ⟨858574571002069259960305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4579064378677702719788293 858574571002069259960305)
                      ·
                        rfl

theorem cell23_1672068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1672068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672068 prefixEnd_1672068 := by exact prefixLift 1672068
  have htrace : WordTrace (prefixWord ++ tailWord_1672068) baseStart_1672068 baseEnd_1672068 := by
    simpa [prefixWord, tailWord_1672068, baseEnd_1672068] using wordTrace_append hprefix tailTrace_1672068
  have hstable : (prefixWord ++ tailWord_1672068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672068).length < 2 ^ (prefixWord ++ tailWord_1672068).sum := by decide
  have hdescent : baseEnd_1672068 < baseStart_1672068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672072 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_1672072 : Nat := 118140960795 + 1672072 * 2 ^ 59
def prefixEnd_1672072 : Nat := 4983230072969 + 3 ^ 40 * 1672072 * 2
def baseEnd_1672072 : Nat := 858576624924687244310287

theorem tailTrace_1672072 : CollatzResearch.WordTrace tailWord_1672072 prefixEnd_1672072 858576624924687244310287 := by
  unfold tailWord_1672072
  simp only [CollatzResearch.WordTrace]
  refine ⟨30492737999188093003773235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40656983998917457338364313 30492737999188093003773235)
  ·
    refine ⟨45739106998782139505659853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30492737999188093003773235 45739106998782139505659853)
    ·
      refine ⟨17152165124543302314622445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45739106998782139505659853 17152165124543302314622445)
      ·
        refine ⟨6432061921703738367983417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17152165124543302314622445 6432061921703738367983417)
        ·
          refine ⟨4824046441277803775987563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6432061921703738367983417 4824046441277803775987563)
          ·
            refine ⟨7236069661916705663981345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824046441277803775987563 7236069661916705663981345)
            ·
              refine ⟨5427052246437529247986009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7236069661916705663981345 5427052246437529247986009)
              ·
                refine ⟨4070289184828146935989507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5427052246437529247986009 4070289184828146935989507)
                ·
                  refine ⟨6105433777242220403984261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070289184828146935989507 6105433777242220403984261)
                  ·
                    refine ⟨1144768833232916325747049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105433777242220403984261 1144768833232916325747049)
                    ·
                      refine ⟨858576624924687244310287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144768833232916325747049 858576624924687244310287)
                      ·
                        rfl

theorem cell23_1672072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_1672072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672072 prefixEnd_1672072 := by exact prefixLift 1672072
  have htrace : WordTrace (prefixWord ++ tailWord_1672072) baseStart_1672072 baseEnd_1672072 := by
    simpa [prefixWord, tailWord_1672072, baseEnd_1672072] using wordTrace_append hprefix tailTrace_1672072
  have hstable : (prefixWord ++ tailWord_1672072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672072).length < 2 ^ (prefixWord ++ tailWord_1672072).sum := by decide
  have hdescent : baseEnd_1672072 < baseStart_1672072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672095 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 7]
def baseStart_1672095 : Nat := 118140960795 + 1672095 * 2 ^ 59
def prefixEnd_1672095 : Nat := 4983230072969 + 3 ^ 40 * 1672095 * 2
def baseEnd_1672095 : Nat := 95398714997748961591409

theorem tailTrace_1672095 : CollatzResearch.WordTrace tailWord_1672095 prefixEnd_1672095 95398714997748961591409 := by
  unfold tailWord_1672095
  simp only [CollatzResearch.WordTrace]
  refine ⟨60986314877292860935633739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40657543251528573957089159 60986314877292860935633739)
  ·
    refine ⟨91479472315939291403450609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60986314877292860935633739 91479472315939291403450609)
    ·
      refine ⟨68609604236954468552587957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91479472315939291403450609 68609604236954468552587957)
      ·
        refine ⟨6432150397214481426805121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68609604236954468552587957 6432150397214481426805121)
        ·
          refine ⟨4824112797910861070103841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6432150397214481426805121 4824112797910861070103841)
          ·
            refine ⟨3618084598433145802577881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4824112797910861070103841 3618084598433145802577881)
            ·
              refine ⟨2713563448824859351933411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618084598433145802577881 2713563448824859351933411)
              ·
                refine ⟨4070345173237289027900117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713563448824859351933411 4070345173237289027900117)
                ·
                  refine ⟨95398714997748961591409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4070345173237289027900117 95398714997748961591409)
                  ·
                    rfl

theorem cell23_1672095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 7].length) (baseStart_1672095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672095 prefixEnd_1672095 := by exact prefixLift 1672095
  have htrace : WordTrace (prefixWord ++ tailWord_1672095) baseStart_1672095 baseEnd_1672095 := by
    simpa [prefixWord, tailWord_1672095, baseEnd_1672095] using wordTrace_append hprefix tailTrace_1672095
  have hstable : (prefixWord ++ tailWord_1672095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672095).length < 2 ^ (prefixWord ++ tailWord_1672095).sum := by decide
  have hdescent : baseEnd_1672095 < baseStart_1672095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672108 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_1672108 : Nat := 118140960795 + 1672108 * 2 ^ 59
def prefixEnd_1672108 : Nat := 4983230072969 + 3 ^ 40 * 1672108 * 2
def baseEnd_1672108 : Nat := 286198370076083034486707

theorem tailTrace_1672108 : CollatzResearch.WordTrace tailWord_1672108 prefixEnd_1672108 286198370076083034486707 := by
  unfold tailWord_1672108
  simp only [CollatzResearch.WordTrace]
  refine ⟨30493394513122882077928489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40657859350830509437237985 30493394513122882077928489)
  ·
    refine ⟨22870045884842161558446367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30493394513122882077928489 22870045884842161558446367)
    ·
      refine ⟨34305068827263242337669551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22870045884842161558446367 34305068827263242337669551)
      ·
        refine ⟨51457603240894863506504327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34305068827263242337669551 51457603240894863506504327)
        ·
          refine ⟨77186404861342295259756491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51457603240894863506504327 77186404861342295259756491)
          ·
            refine ⟨115779607292013442889634737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77186404861342295259756491 115779607292013442889634737)
            ·
              refine ⟨86834705469010082167226053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115779607292013442889634737 86834705469010082167226053)
              ·
                refine ⟨16281507275439390406354885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86834705469010082167226053 16281507275439390406354885)
                ·
                  refine ⟨3052782614144885701191541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16281507275439390406354885 3052782614144885701191541)
                  ·
                    refine ⟨286198370076083034486707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3052782614144885701191541 286198370076083034486707)
                    ·
                      rfl

theorem cell23_1672108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_1672108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672108 prefixEnd_1672108 := by exact prefixLift 1672108
  have htrace : WordTrace (prefixWord ++ tailWord_1672108) baseStart_1672108 baseEnd_1672108 := by
    simpa [prefixWord, tailWord_1672108, baseEnd_1672108] using wordTrace_append hprefix tailTrace_1672108
  have hstable : (prefixWord ++ tailWord_1672108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672108).length < 2 ^ (prefixWord ++ tailWord_1672108).sum := by decide
  have hdescent : baseEnd_1672108 < baseStart_1672108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672145 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_1672145 : Nat := 118140960795 + 1672145 * 2 ^ 59
def prefixEnd_1672145 : Nat := 4983230072969 + 3 ^ 40 * 1672145 * 2
def baseEnd_1672145 : Nat := 858614109012465458697451

theorem tailTrace_1672145 : CollatzResearch.WordTrace tailWord_1672145 prefixEnd_1672145 858614109012465458697451 := by
  unfold tailWord_1672145
  simp only [CollatzResearch.WordTrace]
  refine ⟨60988138527111719474953889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40658759018074479649969259 60988138527111719474953889)
  ·
    refine ⟨45741103895333789606215417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60988138527111719474953889 45741103895333789606215417)
    ·
      refine ⟨34305827921500342204661563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45741103895333789606215417 34305827921500342204661563)
      ·
        refine ⟨51458741882250513306992345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34305827921500342204661563 51458741882250513306992345)
        ·
          refine ⟨38594056411687884980244259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51458741882250513306992345 38594056411687884980244259)
          ·
            refine ⟨57891084617531827470366389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38594056411687884980244259 57891084617531827470366389)
            ·
              refine ⟨5427289182893608825346849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57891084617531827470366389 5427289182893608825346849)
              ·
                refine ⟨4070466887170206619010137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5427289182893608825346849 4070466887170206619010137)
                ·
                  refine ⟨3052850165377654964257603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4070466887170206619010137 3052850165377654964257603)
                  ·
                    refine ⟨4579275248066482446386405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3052850165377654964257603 4579275248066482446386405)
                    ·
                      refine ⟨858614109012465458697451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4579275248066482446386405 858614109012465458697451)
                      ·
                        rfl

theorem cell23_1672145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_1672145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672145 prefixEnd_1672145 := by exact prefixLift 1672145
  have htrace : WordTrace (prefixWord ++ tailWord_1672145) baseStart_1672145 baseEnd_1672145 := by
    simpa [prefixWord, tailWord_1672145, baseEnd_1672145] using wordTrace_append hprefix tailTrace_1672145
  have hstable : (prefixWord ++ tailWord_1672145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672145).length < 2 ^ (prefixWord ++ tailWord_1672145).sum := by decide
  have hdescent : baseEnd_1672145 < baseStart_1672145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672202 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 6]
def baseStart_1672202 : Nat := 118140960795 + 1672202 * 2 ^ 59
def prefixEnd_1672202 : Nat := 4983230072969 + 3 ^ 40 * 1672202 * 2
def baseEnd_1672202 : Nat := 95404819712196859520521

theorem tailTrace_1672202 : CollatzResearch.WordTrace tailWord_1672202 prefixEnd_1672202 95404819712196859520521 := by
  unfold tailWord_1672202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15247554371976304552444715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40660144991936812139852573 15247554371976304552444715)
  ·
    refine ⟨22871331557964456828667073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15247554371976304552444715 22871331557964456828667073)
    ·
      refine ⟨17153498668473342621500305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22871331557964456828667073 17153498668473342621500305)
      ·
        refine ⟨12865124001355006966125229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17153498668473342621500305 12865124001355006966125229)
        ·
          refine ⟨4824421500508127612296961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12865124001355006966125229 4824421500508127612296961)
          ·
            refine ⟨3618316125381095709222721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4824421500508127612296961 3618316125381095709222721)
            ·
              refine ⟨2713737094035821781917041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618316125381095709222721 2713737094035821781917041)
              ·
                refine ⟨2035302820526866336437781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2713737094035821781917041 2035302820526866336437781)
                ·
                  refine ⟨95404819712196859520521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2035302820526866336437781 95404819712196859520521)
                  ·
                    rfl

theorem cell23_1672202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_1672202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672202 prefixEnd_1672202 := by exact prefixLift 1672202
  have htrace : WordTrace (prefixWord ++ tailWord_1672202) baseStart_1672202 baseEnd_1672202 := by
    simpa [prefixWord, tailWord_1672202, baseEnd_1672202] using wordTrace_append hprefix tailTrace_1672202
  have hstable : (prefixWord ++ tailWord_1672202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672202).length < 2 ^ (prefixWord ++ tailWord_1672202).sum := by decide
  have hdescent : baseEnd_1672202 < baseStart_1672202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672206 : List Nat := [4, 1, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_1672206 : Nat := 118140960795 + 1672206 * 2 ^ 59
def prefixEnd_1672206 : Nat := 4983230072969 + 3 ^ 40 * 1672206 * 2
def baseEnd_1672206 : Nat := 286215143777463240011557

theorem tailTrace_1672206 : CollatzResearch.WordTrace tailWord_1672206 prefixEnd_1672206 286215143777463240011557 := by
  unfold tailWord_1672206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7623795422486340861615559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40660242253260484595282981 7623795422486340861615559)
  ·
    refine ⟨11435693133729511292423339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7623795422486340861615559 11435693133729511292423339)
    ·
      refine ⟨17153539700594266938635009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11435693133729511292423339 17153539700594266938635009)
      ·
        refine ⟨12865154775445700203976257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17153539700594266938635009 12865154775445700203976257)
        ·
          refine ⟨9648866081584275152982193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12865154775445700203976257 9648866081584275152982193)
          ·
            refine ⟨7236649561188206364736645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9648866081584275152982193 7236649561188206364736645)
            ·
              refine ⟨1356871792722788693388121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7236649561188206364736645 1356871792722788693388121)
              ·
                refine ⟨1017653844542091520041091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356871792722788693388121 1017653844542091520041091)
                ·
                  refine ⟨1526480766813137280061637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017653844542091520041091 1526480766813137280061637)
                  ·
                    refine ⟨286215143777463240011557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1526480766813137280061637 286215143777463240011557)
                    ·
                      rfl

theorem cell23_1672206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_1672206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672206 prefixEnd_1672206 := by exact prefixLift 1672206
  have htrace : WordTrace (prefixWord ++ tailWord_1672206) baseStart_1672206 baseEnd_1672206 := by
    simpa [prefixWord, tailWord_1672206, baseEnd_1672206] using wordTrace_append hprefix tailTrace_1672206
  have hstable : (prefixWord ++ tailWord_1672206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672206).length < 2 ^ (prefixWord ++ tailWord_1672206).sum := by decide
  have hdescent : baseEnd_1672206 < baseStart_1672206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672208 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_1672208 : Nat := 118140960795 + 1672208 * 2 ^ 59
def prefixEnd_1672208 : Nat := 4983230072969 + 3 ^ 40 * 1672208 * 2
def baseEnd_1672208 : Nat := 858646458293698712209661

theorem tailTrace_1672208 : CollatzResearch.WordTrace tailWord_1672208 prefixEnd_1672208 858646458293698712209661 := by
  unfold tailWord_1672208
  simp only [CollatzResearch.WordTrace]
  refine ⟨30495218162941740617248639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40660290883922320822998185 30495218162941740617248639)
  ·
    refine ⟨45742827244412610925872959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30495218162941740617248639 45742827244412610925872959)
    ·
      refine ⟨68614240866618916388809439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45742827244412610925872959 68614240866618916388809439)
      ·
        refine ⟨102921361299928374583214159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68614240866618916388809439 102921361299928374583214159)
        ·
          refine ⟨154382041949892561874821239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102921361299928374583214159 154382041949892561874821239)
          ·
            refine ⟨231573062924838842812231859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154382041949892561874821239 231573062924838842812231859)
            ·
              refine ⟨347359594387258264218347789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231573062924838842812231859 347359594387258264218347789)
              ·
                refine ⟨130259847895221849081880421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347359594387258264218347789 130259847895221849081880421)
                ·
                  refine ⟨24423721480354096702852579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130259847895221849081880421 24423721480354096702852579)
                  ·
                    refine ⟨36635582220531145054278869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24423721480354096702852579 36635582220531145054278869)
                    ·
                      refine ⟨858646458293698712209661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36635582220531145054278869 858646458293698712209661)
                      ·
                        rfl

theorem cell23_1672208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_1672208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672208 prefixEnd_1672208 := by exact prefixLift 1672208
  have htrace : WordTrace (prefixWord ++ tailWord_1672208) baseStart_1672208 baseEnd_1672208 := by
    simpa [prefixWord, tailWord_1672208, baseEnd_1672208] using wordTrace_append hprefix tailTrace_1672208
  have hstable : (prefixWord ++ tailWord_1672208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672208).length < 2 ^ (prefixWord ++ tailWord_1672208).sum := by decide
  have hdescent : baseEnd_1672208 < baseStart_1672208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672235 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 4]
def baseStart_1672235 : Nat := 118140960795 + 1672235 * 2 ^ 59
def prefixEnd_1672235 : Nat := 4983230072969 + 3 ^ 40 * 1672235 * 2
def baseEnd_1672235 : Nat := 858660322271370106572037

theorem tailTrace_1672235 : CollatzResearch.WordTrace tailWord_1672235 prefixEnd_1672235 858660322271370106572037 := by
  unfold tailWord_1672235
  simp only [CollatzResearch.WordTrace]
  refine ⟨60991421096785664845730159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40660947397857109897153439 60991421096785664845730159)
  ·
    refine ⟨91487131645178497268595239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60991421096785664845730159 91487131645178497268595239)
    ·
      refine ⟨137230697467767745902892859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91487131645178497268595239 137230697467767745902892859)
      ·
        refine ⟨205846046201651618854339289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137230697467767745902892859 205846046201651618854339289)
        ·
          refine ⟨154384534651238714140754467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205846046201651618854339289 154384534651238714140754467)
          ·
            refine ⟨231576801976858071211131701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154384534651238714140754467 231576801976858071211131701)
            ·
              refine ⟨21710325185330444176043597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231576801976858071211131701 21710325185330444176043597)
              ·
                refine ⟨8141371944498916566016349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21710325185330444176043597 8141371944498916566016349)
                ·
                  refine ⟨3053014479187093712256131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8141371944498916566016349 3053014479187093712256131)
                  ·
                    refine ⟨4579521718780640568384197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3053014479187093712256131 4579521718780640568384197)
                    ·
                      refine ⟨858660322271370106572037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4579521718780640568384197 858660322271370106572037)
                      ·
                        rfl

theorem cell23_1672235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 4].length) (baseStart_1672235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672235 prefixEnd_1672235 := by exact prefixLift 1672235
  have htrace : WordTrace (prefixWord ++ tailWord_1672235) baseStart_1672235 baseEnd_1672235 := by
    simpa [prefixWord, tailWord_1672235, baseEnd_1672235] using wordTrace_append hprefix tailTrace_1672235
  have hstable : (prefixWord ++ tailWord_1672235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672235).length < 2 ^ (prefixWord ++ tailWord_1672235).sum := by decide
  have hdescent : baseEnd_1672235 < baseStart_1672235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672249 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 1, 5]
def baseStart_1672249 : Nat := 118140960795 + 1672249 * 2 ^ 59
def prefixEnd_1672249 : Nat := 4983230072969 + 3 ^ 40 * 1672249 * 2
def baseEnd_1672249 : Nat := 286222503666844350598991

theorem tailTrace_1672249 : CollatzResearch.WordTrace tailWord_1672249 prefixEnd_1672249 286222503666844350598991 := by
  unfold tailWord_1672249
  simp only [CollatzResearch.WordTrace]
  refine ⟨60991931718734945236739801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40661287812489963491159867 60991931718734945236739801)
  ·
    refine ⟨45743948789051208927554851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60991931718734945236739801 45743948789051208927554851)
    ·
      refine ⟨68615923183576813391332277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45743948789051208927554851 68615923183576813391332277)
      ·
        refine ⟨6432742798460326255437401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68615923183576813391332277 6432742798460326255437401)
        ·
          refine ⟨4824557098845244691578051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6432742798460326255437401 4824557098845244691578051)
          ·
            refine ⟨7236835648267867037367077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824557098845244691578051 7236835648267867037367077)
            ·
              refine ⟨1356906684050225069506327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7236835648267867037367077 1356906684050225069506327)
              ·
                refine ⟨2035360026075337604259491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356906684050225069506327 2035360026075337604259491)
                ·
                  refine ⟨3053040039113006406389237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035360026075337604259491 3053040039113006406389237)
                  ·
                    refine ⟨286222503666844350598991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3053040039113006406389237 286222503666844350598991)
                    ·
                      rfl

theorem cell23_1672249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 5].length) (baseStart_1672249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672249 prefixEnd_1672249 := by exact prefixLift 1672249
  have htrace : WordTrace (prefixWord ++ tailWord_1672249) baseStart_1672249 baseEnd_1672249 := by
    simpa [prefixWord, tailWord_1672249, baseEnd_1672249] using wordTrace_append hprefix tailTrace_1672249
  have hstable : (prefixWord ++ tailWord_1672249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672249).length < 2 ^ (prefixWord ++ tailWord_1672249).sum := by decide
  have hdescent : baseEnd_1672249 < baseStart_1672249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672255 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_1672255 : Nat := 118140960795 + 1672255 * 2 ^ 59
def prefixEnd_1672255 : Nat := 4983230072969 + 3 ^ 40 * 1672255 * 2
def baseEnd_1672255 : Nat := 858670591884460028321945

theorem tailTrace_1672255 : CollatzResearch.WordTrace tailWord_1672255 prefixEnd_1672255 858670591884460028321945 := by
  unfold tailWord_1672255
  simp only [CollatzResearch.WordTrace]
  refine ⟨60992150556713208261458219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40661433704475472174305479 60992150556713208261458219)
  ·
    refine ⟨91488225835069812392187329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60992150556713208261458219 91488225835069812392187329)
    ·
      refine ⟨68616169376302359294140497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91488225835069812392187329 68616169376302359294140497)
      ·
        refine ⟨51462127032226769470605373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68616169376302359294140497 51462127032226769470605373)
        ·
          refine ⟨19298297637085038551477015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51462127032226769470605373 19298297637085038551477015)
          ·
            refine ⟨28947446455627557827215523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19298297637085038551477015 28947446455627557827215523)
            ·
              refine ⟨43421169683441336740823285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28947446455627557827215523 43421169683441336740823285)
              ·
                refine ⟨4070734657822625319452183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43421169683441336740823285 4070734657822625319452183)
                ·
                  refine ⟨6106101986733937979178275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070734657822625319452183 6106101986733937979178275)
                  ·
                    refine ⟨9159152980100906968767413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6106101986733937979178275 9159152980100906968767413)
                    ·
                      refine ⟨858670591884460028321945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9159152980100906968767413 858670591884460028321945)
                      ·
                        rfl

theorem cell23_1672255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_1672255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672255 prefixEnd_1672255 := by exact prefixLift 1672255
  have htrace : WordTrace (prefixWord ++ tailWord_1672255) baseStart_1672255 baseEnd_1672255 := by
    simpa [prefixWord, tailWord_1672255, baseEnd_1672255] using wordTrace_append hprefix tailTrace_1672255
  have hstable : (prefixWord ++ tailWord_1672255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672255).length < 2 ^ (prefixWord ++ tailWord_1672255).sum := by decide
  have hdescent : baseEnd_1672255 < baseStart_1672255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672309 : List Nat := [1, 3, 4, 3, 1, 2, 9]
def baseStart_1672309 : Nat := 118140960795 + 1672309 * 2 ^ 59
def prefixEnd_1672309 : Nat := 4983230072969 + 3 ^ 40 * 1672309 * 2
def baseEnd_1672309 : Nat := 10601213825182750827737

theorem tailTrace_1672309 : CollatzResearch.WordTrace tailWord_1672309 prefixEnd_1672309 10601213825182750827737 := by
  unfold tailWord_1672309
  simp only [CollatzResearch.WordTrace]
  refine ⟨60994120098517575483923981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40662746732345050322615987 60994120098517575483923981)
  ·
    refine ⟨22872795036944090806471493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60994120098517575483923981 22872795036944090806471493)
    ·
      refine ⟨4288649069427017026213405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22872795036944090806471493 4288649069427017026213405)
      ·
        refine ⟨1608243401035131384830027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4288649069427017026213405 1608243401035131384830027)
        ·
          refine ⟨2412365101552697077245041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608243401035131384830027 2412365101552697077245041)
          ·
            refine ⟨1809273826164522807933781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2412365101552697077245041 1809273826164522807933781)
            ·
              refine ⟨10601213825182750827737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1809273826164522807933781 10601213825182750827737)
              ·
                rfl

theorem cell23_1672309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 9].length) (baseStart_1672309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672309 prefixEnd_1672309 := by exact prefixLift 1672309
  have htrace : WordTrace (prefixWord ++ tailWord_1672309) baseStart_1672309 baseEnd_1672309 := by
    simpa [prefixWord, tailWord_1672309, baseEnd_1672309] using wordTrace_append hprefix tailTrace_1672309
  have hstable : (prefixWord ++ tailWord_1672309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672309).length < 2 ^ (prefixWord ++ tailWord_1672309).sum := by decide
  have hdescent : baseEnd_1672309 < baseStart_1672309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672346 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1672346 : Nat := 118140960795 + 1672346 * 2 ^ 59
def prefixEnd_1672346 : Nat := 4983230072969 + 3 ^ 40 * 1672346 * 2
def baseEnd_1672346 : Nat := 858717318624019172284027

theorem tailTrace_1672346 : CollatzResearch.WordTrace tailWord_1672346 prefixEnd_1672346 858717318624019172284027 := by
  unfold tailWord_1672346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15248867399845882700755223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40663646399589020535347261 15248867399845882700755223)
  ·
    refine ⟨22873301099768824051132835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15248867399845882700755223 22873301099768824051132835)
    ·
      refine ⟨34309951649653236076699253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22873301099768824051132835 34309951649653236076699253)
      ·
        refine ⟨3216557967154990882190555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34309951649653236076699253 3216557967154990882190555)
        ·
          refine ⟨4824836950732486323285833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216557967154990882190555 4824836950732486323285833)
          ·
            refine ⟨3618627713049364742464375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4824836950732486323285833 3618627713049364742464375)
            ·
              refine ⟨5427941569574047113696563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618627713049364742464375 5427941569574047113696563)
              ·
                refine ⟨8141912354361070670544845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427941569574047113696563 8141912354361070670544845)
                ·
                  refine ⟨3053217132885401501454317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8141912354361070670544845 3053217132885401501454317)
                  ·
                    refine ⟨1144956424832025563045369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3053217132885401501454317 1144956424832025563045369)
                    ·
                      refine ⟨858717318624019172284027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1144956424832025563045369 858717318624019172284027)
                      ·
                        rfl

theorem cell23_1672346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1672346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672346 prefixEnd_1672346 := by exact prefixLift 1672346
  have htrace : WordTrace (prefixWord ++ tailWord_1672346) baseStart_1672346 baseEnd_1672346 := by
    simpa [prefixWord, tailWord_1672346, baseEnd_1672346] using wordTrace_append hprefix tailTrace_1672346
  have hstable : (prefixWord ++ tailWord_1672346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672346).length < 2 ^ (prefixWord ++ tailWord_1672346).sum := by decide
  have hdescent : baseEnd_1672346 < baseStart_1672346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672392 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_1672392 : Nat := 118140960795 + 1672392 * 2 ^ 59
def prefixEnd_1672392 : Nat := 4983230072969 + 3 ^ 40 * 1672392 * 2
def baseEnd_1672392 : Nat := 858740938734125992308815

theorem tailTrace_1672392 : CollatzResearch.WordTrace tailWord_1672392 prefixEnd_1672392 858740938734125992308815 := by
  unfold tailWord_1672392
  simp only [CollatzResearch.WordTrace]
  refine ⟨30498573678608440329597715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40664764904811253772796953 30498573678608440329597715)
  ·
    refine ⟨45747860517912660494396573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30498573678608440329597715 45747860517912660494396573)
    ·
      refine ⟨17155447694217247685398715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45747860517912660494396573 17155447694217247685398715)
      ·
        refine ⟨25733171541325871528098073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17155447694217247685398715 25733171541325871528098073)
        ·
          refine ⟨19299878655994403646073555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25733171541325871528098073 19299878655994403646073555)
          ·
            refine ⟨28949817983991605469110333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19299878655994403646073555 28949817983991605469110333)
            ·
              refine ⟨10856181743996852050916375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28949817983991605469110333 10856181743996852050916375)
              ·
                refine ⟨16284272615995278076374563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10856181743996852050916375 16284272615995278076374563)
                ·
                  refine ⟨24426408923992917114561845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16284272615995278076374563 24426408923992917114561845)
                  ·
                    refine ⟨2289975836624335979490173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24426408923992917114561845 2289975836624335979490173)
                    ·
                      refine ⟨858740938734125992308815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2289975836624335979490173 858740938734125992308815)
                      ·
                        rfl

theorem cell23_1672392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_1672392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672392 prefixEnd_1672392 := by exact prefixLift 1672392
  have htrace : WordTrace (prefixWord ++ tailWord_1672392) baseStart_1672392 baseEnd_1672392 := by
    simpa [prefixWord, tailWord_1672392, baseEnd_1672392] using wordTrace_append hprefix tailTrace_1672392
  have hstable : (prefixWord ++ tailWord_1672392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672392).length < 2 ^ (prefixWord ++ tailWord_1672392).sum := by decide
  have hdescent : baseEnd_1672392 < baseStart_1672392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672459 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 3, 4]
def baseStart_1672459 : Nat := 118140960795 + 1672459 * 2 ^ 59
def prefixEnd_1672459 : Nat := 4983230072969 + 3 ^ 40 * 1672459 * 2
def baseEnd_1672459 : Nat := 286258447312659076723669

theorem tailTrace_1672459 : CollatzResearch.WordTrace tailWord_1672459 prefixEnd_1672459 286258447312659076723669 := by
  unfold tailWord_1672459
  simp only [CollatzResearch.WordTrace]
  refine ⟨60999591047974151101884431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40666394031982767401256287 60999591047974151101884431)
  ·
    refine ⟨91499386571961226652826647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60999591047974151101884431 91499386571961226652826647)
    ·
      refine ⟨137249079857941839979239971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91499386571961226652826647 137249079857941839979239971)
      ·
        refine ⟨205873619786912759968859957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137249079857941839979239971 205873619786912759968859957)
        ·
          refine ⟨19300651855023071247080621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205873619786912759968859957 19300651855023071247080621)
          ·
            refine ⟨7237744445633651717655233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19300651855023071247080621 7237744445633651717655233)
            ·
              refine ⟨5428308334225238788241425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7237744445633651717655233 5428308334225238788241425)
              ·
                refine ⟨4071231250668929091181069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5428308334225238788241425 4071231250668929091181069)
                ·
                  refine ⟨1526711719000848409192901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4071231250668929091181069 1526711719000848409192901)
                  ·
                    refine ⟨286258447312659076723669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1526711719000848409192901 286258447312659076723669)
                    ·
                      rfl

theorem cell23_1672459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 4].length) (baseStart_1672459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672459 prefixEnd_1672459 := by exact prefixLift 1672459
  have htrace : WordTrace (prefixWord ++ tailWord_1672459) baseStart_1672459 baseEnd_1672459 := by
    simpa [prefixWord, tailWord_1672459, baseEnd_1672459] using wordTrace_append hprefix tailTrace_1672459
  have hstable : (prefixWord ++ tailWord_1672459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672459).length < 2 ^ (prefixWord ++ tailWord_1672459).sum := by decide
  have hdescent : baseEnd_1672459 < baseStart_1672459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672469 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_1672469 : Nat := 118140960795 + 1672469 * 2 ^ 59
def prefixEnd_1672469 : Nat := 4983230072969 + 3 ^ 40 * 1672469 * 2
def baseEnd_1672469 : Nat := 858780476744522191045961

theorem tailTrace_1672469 : CollatzResearch.WordTrace tailWord_1672469 prefixEnd_1672469 858780476744522191045961 := by
  unfold tailWord_1672469
  simp only [CollatzResearch.WordTrace]
  refine ⟨60999955777937922809748461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40666637185291948539832307 60999955777937922809748461)
  ·
    refine ⟨22874983416726721053655673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60999955777937922809748461 22874983416726721053655673)
    ·
      refine ⟨17156237562545040790241755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22874983416726721053655673 17156237562545040790241755)
      ·
        refine ⟨25734356343817561185362633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17156237562545040790241755 25734356343817561185362633)
        ·
          refine ⟨19300767257863170889021975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25734356343817561185362633 19300767257863170889021975)
          ·
            refine ⟨28951150886794756333532963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19300767257863170889021975 28951150886794756333532963)
            ·
              refine ⟨43426726330192134500299445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28951150886794756333532963 43426726330192134500299445)
              ·
                refine ⟨4071255593455512609403073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43426726330192134500299445 4071255593455512609403073)
                ·
                  refine ⟨3053441695091634457052305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4071255593455512609403073 3053441695091634457052305)
                  ·
                    refine ⟨2290081271318725842789229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3053441695091634457052305 2290081271318725842789229)
                    ·
                      refine ⟨858780476744522191045961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2290081271318725842789229 858780476744522191045961)
                      ·
                        rfl

theorem cell23_1672469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_1672469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672469 prefixEnd_1672469 := by exact prefixLift 1672469
  have htrace : WordTrace (prefixWord ++ tailWord_1672469) baseStart_1672469 baseEnd_1672469 := by
    simpa [prefixWord, tailWord_1672469, baseEnd_1672469] using wordTrace_append hprefix tailTrace_1672469
  have hstable : (prefixWord ++ tailWord_1672469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672469).length < 2 ^ (prefixWord ++ tailWord_1672469).sum := by decide
  have hdescent : baseEnd_1672469 < baseStart_1672469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672472 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 8]
def baseStart_1672472 : Nat := 118140960795 + 1672472 * 2 ^ 59
def prefixEnd_1672472 : Nat := 4983230072969 + 3 ^ 40 * 1672472 * 2
def baseEnd_1672472 : Nat := 95420224131831742145383

theorem tailTrace_1672472 : CollatzResearch.WordTrace tailWord_1672472 prefixEnd_1672472 95420224131831742145383 := by
  unfold tailWord_1672472
  simp only [CollatzResearch.WordTrace]
  refine ⟨30500032598463527161053835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40666710131284702881405113 30500032598463527161053835)
  ·
    refine ⟨45750048897695290741580753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30500032598463527161053835 45750048897695290741580753)
    ·
      refine ⟨34312536673271468056185565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45750048897695290741580753 34312536673271468056185565)
      ·
        refine ⟨12867201252476800521069587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34312536673271468056185565 12867201252476800521069587)
        ·
          refine ⟨19300801878715200781604381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12867201252476800521069587 19300801878715200781604381)
          ·
            refine ⟨7237800704518200293101643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19300801878715200781604381 7237800704518200293101643)
            ·
              refine ⟨10856701056777300439652465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7237800704518200293101643 10856701056777300439652465)
              ·
                refine ⟨8142525792582975329739349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10856701056777300439652465 8142525792582975329739349)
                ·
                  refine ⟨95420224131831742145383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8142525792582975329739349 95420224131831742145383)
                  ·
                    rfl

theorem cell23_1672472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 8].length) (baseStart_1672472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672472 prefixEnd_1672472 := by exact prefixLift 1672472
  have htrace : WordTrace (prefixWord ++ tailWord_1672472) baseStart_1672472 baseEnd_1672472 := by
    simpa [prefixWord, tailWord_1672472, baseEnd_1672472] using wordTrace_append hprefix tailTrace_1672472
  have hstable : (prefixWord ++ tailWord_1672472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672472).length < 2 ^ (prefixWord ++ tailWord_1672472).sum := by decide
  have hdescent : baseEnd_1672472 < baseStart_1672472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672493 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1672493 : Nat := 118140960795 + 1672493 * 2 ^ 59
def prefixEnd_1672493 : Nat := 4983230072969 + 3 ^ 40 * 1672493 * 2
def baseEnd_1672493 : Nat := 286264266760076699048617

theorem tailTrace_1672493 : CollatzResearch.WordTrace tailWord_1672493 prefixEnd_1672493 286264266760076699048617 := by
  unfold tailWord_1672493
  simp only [CollatzResearch.WordTrace]
  refine ⟨61000831129850974908622133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40667220753233983272414755 61000831129850974908622133)
  ·
    refine ⟨5718827918423528897683325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61000831129850974908622133 5718827918423528897683325)
    ·
      refine ⟨2144560469408823336631247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5718827918423528897683325 2144560469408823336631247)
      ·
        refine ⟨3216840704113235004946871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144560469408823336631247 3216840704113235004946871)
        ·
          refine ⟨4825261056169852507420307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216840704113235004946871 4825261056169852507420307)
          ·
            refine ⟨7237891584254778761130461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825261056169852507420307 7237891584254778761130461)
            ·
              refine ⟨2714209344095542035423923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7237891584254778761130461 2714209344095542035423923)
              ·
                refine ⟨4071314016143313053135885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714209344095542035423923 4071314016143313053135885)
                ·
                  refine ⟨1526742756053742394925957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4071314016143313053135885 1526742756053742394925957)
                  ·
                    refine ⟨286264266760076699048617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1526742756053742394925957 286264266760076699048617)
                    ·
                      rfl

theorem cell23_1672493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1672493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672493 prefixEnd_1672493 := by exact prefixLift 1672493
  have htrace : WordTrace (prefixWord ++ tailWord_1672493) baseStart_1672493 baseEnd_1672493 := by
    simpa [prefixWord, tailWord_1672493, baseEnd_1672493] using wordTrace_append hprefix tailTrace_1672493
  have hstable : (prefixWord ++ tailWord_1672493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672493).length < 2 ^ (prefixWord ++ tailWord_1672493).sum := by decide
  have hdescent : baseEnd_1672493 < baseStart_1672493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672519 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 3, 5]
def baseStart_1672519 : Nat := 118140960795 + 1672519 * 2 ^ 59
def prefixEnd_1672519 : Nat := 4983230072969 + 3 ^ 40 * 1672519 * 2
def baseEnd_1672519 : Nat := 286268716925748998473577

theorem tailTrace_1672519 : CollatzResearch.WordTrace tailWord_1672519 prefixEnd_1672519 286268716925748998473577 := by
  unfold tailWord_1672519
  simp only [CollatzResearch.WordTrace]
  refine ⟨61001779427756781349068611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40667852951837854232712407 61001779427756781349068611)
  ·
    refine ⟨91502669141635172023602917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61001779427756781349068611 91502669141635172023602917)
    ·
      refine ⟨17156750464056594754425547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91502669141635172023602917 17156750464056594754425547)
      ·
        refine ⟨25735125696084892131638321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17156750464056594754425547 25735125696084892131638321)
        ·
          refine ⟨19301344272063669098728741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25735125696084892131638321 19301344272063669098728741)
          ·
            refine ⟨3619002051011937956011639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19301344272063669098728741 3619002051011937956011639)
            ·
              refine ⟨5428503076517906934017459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619002051011937956011639 5428503076517906934017459)
              ·
                refine ⟨8142754614776860401026189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428503076517906934017459 8142754614776860401026189)
                ·
                  refine ⟨3053532980541322650384821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8142754614776860401026189 3053532980541322650384821)
                  ·
                    refine ⟨286268716925748998473577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3053532980541322650384821 286268716925748998473577)
                    ·
                      rfl

theorem cell23_1672519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_1672519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672519 prefixEnd_1672519 := by exact prefixLift 1672519
  have htrace : WordTrace (prefixWord ++ tailWord_1672519) baseStart_1672519 baseEnd_1672519 := by
    simpa [prefixWord, tailWord_1672519, baseEnd_1672519] using wordTrace_append hprefix tailTrace_1672519
  have hstable : (prefixWord ++ tailWord_1672519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672519).length < 2 ^ (prefixWord ++ tailWord_1672519).sum := by decide
  have hdescent : baseEnd_1672519 < baseStart_1672519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672536 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 1, 5]
def baseStart_1672536 : Nat := 118140960795 + 1672536 * 2 ^ 59
def prefixEnd_1672536 : Nat := 4983230072969 + 3 ^ 40 * 1672536 * 2
def baseEnd_1672536 : Nat := 286271626649457809636051

theorem tailTrace_1672536 : CollatzResearch.WordTrace tailWord_1672536 prefixEnd_1672536 286271626649457809636051 := by
  unfold tailWord_1672536
  simp only [CollatzResearch.WordTrace]
  refine ⟨30501199734347596626218731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40668266312463462168291641 30501199734347596626218731)
  ·
    refine ⟨45751799601521394939328097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30501199734347596626218731 45751799601521394939328097)
    ·
      refine ⟨34313849701141046204496073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45751799601521394939328097 34313849701141046204496073)
      ·
        refine ⟨25735387275855784653372055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34313849701141046204496073 25735387275855784653372055)
        ·
          refine ⟨38603080913783676980058083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25735387275855784653372055 38603080913783676980058083)
          ·
            refine ⟨57904621370675515470087125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38603080913783676980058083 57904621370675515470087125)
            ·
              refine ⟨1357139563375207393830167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57904621370675515470087125 1357139563375207393830167)
              ·
                refine ⟨2035709345062811090745251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357139563375207393830167 2035709345062811090745251)
                ·
                  refine ⟨3053564017594216636117877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035709345062811090745251 3053564017594216636117877)
                  ·
                    refine ⟨286271626649457809636051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3053564017594216636117877 286271626649457809636051)
                    ·
                      rfl

theorem cell23_1672536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_1672536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672536 prefixEnd_1672536 := by exact prefixLift 1672536
  have htrace : WordTrace (prefixWord ++ tailWord_1672536) baseStart_1672536 baseEnd_1672536 := by
    simpa [prefixWord, tailWord_1672536, baseEnd_1672536] using wordTrace_append hprefix tailTrace_1672536
  have hstable : (prefixWord ++ tailWord_1672536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672536).length < 2 ^ (prefixWord ++ tailWord_1672536).sum := by decide
  have hdescent : baseEnd_1672536 < baseStart_1672536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672559 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 3]
def baseStart_1672559 : Nat := 118140960795 + 1672559 * 2 ^ 59
def prefixEnd_1672559 : Nat := 4983230072969 + 3 ^ 40 * 1672559 * 2
def baseEnd_1672559 : Nat := 858826690003426838920547

theorem tailTrace_1672559 : CollatzResearch.WordTrace tailWord_1672559 prefixEnd_1672559 858826690003426838920547 := by
  unfold tailWord_1672559
  simp only [CollatzResearch.WordTrace]
  refine ⟨61003238347611868180524731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40668825565074578787016487 61003238347611868180524731)
  ·
    refine ⟨91504857521417802270787097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61003238347611868180524731 91504857521417802270787097)
    ·
      refine ⟨68628643141063351703090323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91504857521417802270787097 68628643141063351703090323)
      ·
        refine ⟨102942964711595027554635485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68628643141063351703090323 102942964711595027554635485)
        ·
          refine ⟨38603611766848135332988307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102942964711595027554635485 38603611766848135332988307)
          ·
            refine ⟨57905417650272202999482461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38603611766848135332988307 57905417650272202999482461)
            ·
              refine ⟨21714531618852076124805923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57905417650272202999482461 21714531618852076124805923)
              ·
                refine ⟨32571797428278114187208885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21714531618852076124805923 32571797428278114187208885)
                ·
                  refine ⟨3053606008901073205050833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32571797428278114187208885 3053606008901073205050833)
                  ·
                    refine ⟨2290204506675804903788125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3053606008901073205050833 2290204506675804903788125)
                    ·
                      refine ⟨858826690003426838920547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2290204506675804903788125 858826690003426838920547)
                      ·
                        rfl

theorem cell23_1672559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_1672559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672559 prefixEnd_1672559 := by exact prefixLift 1672559
  have htrace : WordTrace (prefixWord ++ tailWord_1672559) baseStart_1672559 baseEnd_1672559 := by
    simpa [prefixWord, tailWord_1672559, baseEnd_1672559] using wordTrace_append hprefix tailTrace_1672559
  have hstable : (prefixWord ++ tailWord_1672559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672559).length < 2 ^ (prefixWord ++ tailWord_1672559).sum := by decide
  have hdescent : baseEnd_1672559 < baseStart_1672559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672569 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1672569 : Nat := 118140960795 + 1672569 * 2 ^ 59
def prefixEnd_1672569 : Nat := 4983230072969 + 3 ^ 40 * 1672569 * 2
def baseEnd_1672569 : Nat := 858831824809971799795501

theorem tailTrace_1672569 : CollatzResearch.WordTrace tailWord_1672569 prefixEnd_1672569 858831824809971799795501 := by
  unfold tailWord_1672569
  simp only [CollatzResearch.WordTrace]
  refine ⟨61003603077575639888388761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40669068718383759925592507 61003603077575639888388761)
  ·
    refine ⟨45752702308181729916291571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61003603077575639888388761 45752702308181729916291571)
    ·
      refine ⟨68629053462272594874437357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45752702308181729916291571 68629053462272594874437357)
      ·
        refine ⟨25735895048352223077914009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68629053462272594874437357 25735895048352223077914009)
        ·
          refine ⟨19301921286264167308435507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25735895048352223077914009 19301921286264167308435507)
          ·
            refine ⟨28952881929396250962653261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19301921286264167308435507 28952881929396250962653261)
            ·
              refine ⟨10857330723523594110994973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28952881929396250962653261 10857330723523594110994973)
              ·
                refine ⟨4071499021321347791623115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10857330723523594110994973 4071499021321347791623115)
                ·
                  refine ⟨6107248531982021687434673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071499021321347791623115 6107248531982021687434673)
                  ·
                    refine ⟨4580436398986516265576005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6107248531982021687434673 4580436398986516265576005)
                    ·
                      refine ⟨858831824809971799795501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4580436398986516265576005 858831824809971799795501)
                      ·
                        rfl

theorem cell23_1672569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1672569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672569 prefixEnd_1672569 := by exact prefixLift 1672569
  have htrace : WordTrace (prefixWord ++ tailWord_1672569) baseStart_1672569 baseEnd_1672569 := by
    simpa [prefixWord, tailWord_1672569, baseEnd_1672569] using wordTrace_append hprefix tailTrace_1672569
  have hstable : (prefixWord ++ tailWord_1672569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672569).length < 2 ^ (prefixWord ++ tailWord_1672569).sum := by decide
  have hdescent : baseEnd_1672569 < baseStart_1672569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672573 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_1672573 : Nat := 118140960795 + 1672573 * 2 ^ 59
def prefixEnd_1672573 : Nat := 4983230072969 + 3 ^ 40 * 1672573 * 2
def baseEnd_1672573 : Nat := 858833878732589784145483

theorem tailTrace_1672573 : CollatzResearch.WordTrace tailWord_1672573 prefixEnd_1672573 858833878732589784145483 := by
  unfold tailWord_1672573
  simp only [CollatzResearch.WordTrace]
  refine ⟨61003748969561148571534373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40669165979707432381022915 61003748969561148571534373)
  ·
    refine ⟨11438202931792715357162695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61003748969561148571534373 11438202931792715357162695)
    ·
      refine ⟨17157304397689073035744043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11438202931792715357162695 17157304397689073035744043)
      ·
        refine ⟨25735956596533609553616065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17157304397689073035744043 25735956596533609553616065)
        ·
          refine ⟨19301967447400207165212049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25735956596533609553616065 19301967447400207165212049)
          ·
            refine ⟨14476475585550155373909037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19301967447400207165212049 14476475585550155373909037)
            ·
              refine ⟨5428678344581308265215889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14476475585550155373909037 5428678344581308265215889)
              ·
                refine ⟨4071508758435981198911917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5428678344581308265215889 4071508758435981198911917)
                ·
                  refine ⟨1526815784413492949591969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4071508758435981198911917 1526815784413492949591969)
                  ·
                    refine ⟨1145111838310119712193977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1526815784413492949591969 1145111838310119712193977)
                    ·
                      refine ⟨858833878732589784145483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145111838310119712193977 858833878732589784145483)
                      ·
                        rfl

theorem cell23_1672573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_1672573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672573 prefixEnd_1672573 := by exact prefixLift 1672573
  have htrace : WordTrace (prefixWord ++ tailWord_1672573) baseStart_1672573 baseEnd_1672573 := by
    simpa [prefixWord, tailWord_1672573, baseEnd_1672573] using wordTrace_append hprefix tailTrace_1672573
  have hstable : (prefixWord ++ tailWord_1672573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672573).length < 2 ^ (prefixWord ++ tailWord_1672573).sum := by decide
  have hdescent : baseEnd_1672573 < baseStart_1672573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672577 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_1672577 : Nat := 118140960795 + 1672577 * 2 ^ 59
def prefixEnd_1672577 : Nat := 4983230072969 + 3 ^ 40 * 1672577 * 2
def baseEnd_1672577 : Nat := 858835932655207768495465

theorem tailTrace_1672577 : CollatzResearch.WordTrace tailWord_1672577 prefixEnd_1672577 858835932655207768495465 := by
  unfold tailWord_1672577
  simp only [CollatzResearch.WordTrace]
  refine ⟨61003894861546657254679985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40669263241031104836453323 61003894861546657254679985)
  ·
    refine ⟨45752921146159992941009989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61003894861546657254679985 45752921146159992941009989)
    ·
      refine ⟨8578672714904998676439373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45752921146159992941009989 8578672714904998676439373)
      ·
        refine ⟨3217002268089374503664765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8578672714904998676439373 3217002268089374503664765)
        ·
          refine ⟨1206375850533515438874287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3217002268089374503664765 1206375850533515438874287)
          ·
            refine ⟨1809563775800273158311431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206375850533515438874287 1809563775800273158311431)
            ·
              refine ⟨2714345663700409737467147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809563775800273158311431 2714345663700409737467147)
              ·
                refine ⟨4071518495550614606200721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714345663700409737467147 4071518495550614606200721)
                ·
                  refine ⟨3053638871662960954650541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4071518495550614606200721 3053638871662960954650541)
                  ·
                    refine ⟨1145114576873610357993953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3053638871662960954650541 1145114576873610357993953)
                    ·
                      refine ⟨858835932655207768495465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145114576873610357993953 858835932655207768495465)
                      ·
                        rfl

theorem cell23_1672577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_1672577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672577 prefixEnd_1672577 := by exact prefixLift 1672577
  have htrace : WordTrace (prefixWord ++ tailWord_1672577) baseStart_1672577 baseEnd_1672577 := by
    simpa [prefixWord, tailWord_1672577, baseEnd_1672577] using wordTrace_append hprefix tailTrace_1672577
  have hstable : (prefixWord ++ tailWord_1672577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672577).length < 2 ^ (prefixWord ++ tailWord_1672577).sum := by decide
  have hdescent : baseEnd_1672577 < baseStart_1672577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672600 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 2, 4]
def baseStart_1672600 : Nat := 118140960795 + 1672600 * 2 ^ 59
def prefixEnd_1672600 : Nat := 4983230072969 + 3 ^ 40 * 1672600 * 2
def baseEnd_1672600 : Nat := 286282580903420392835953

theorem tailTrace_1672600 : CollatzResearch.WordTrace tailWord_1672600 prefixEnd_1672600 286282580903420392835953 := by
  unfold tailWord_1672600
  simp only [CollatzResearch.WordTrace]
  refine ⟨30502366870231666091383627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40669822493642221455178169 30502366870231666091383627)
  ·
    refine ⟨45753550305347499137075441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30502366870231666091383627 45753550305347499137075441)
    ·
      refine ⟨34315162729010624352806581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45753550305347499137075441 34315162729010624352806581)
      ·
        refine ⟨3217046505844746033075617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34315162729010624352806581 3217046505844746033075617)
        ·
          refine ⟨2412784879383559524806713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3217046505844746033075617 2412784879383559524806713)
          ·
            refine ⟨1809588659537669643605035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2412784879383559524806713 1809588659537669643605035)
            ·
              refine ⟨2714382989306504465407553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809588659537669643605035 2714382989306504465407553)
              ·
                refine ⟨2035787241979878349055665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2714382989306504465407553 2035787241979878349055665)
                ·
                  refine ⟨1526840431484908761791749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2035787241979878349055665 1526840431484908761791749)
                  ·
                    refine ⟨286282580903420392835953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1526840431484908761791749 286282580903420392835953)
                    ·
                      rfl

theorem cell23_1672600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_1672600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672600 prefixEnd_1672600 := by exact prefixLift 1672600
  have htrace : WordTrace (prefixWord ++ tailWord_1672600) baseStart_1672600 baseEnd_1672600 := by
    simpa [prefixWord, tailWord_1672600, baseEnd_1672600] using wordTrace_append hprefix tailTrace_1672600
  have hstable : (prefixWord ++ tailWord_1672600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672600).length < 2 ^ (prefixWord ++ tailWord_1672600).sum := by decide
  have hdescent : baseEnd_1672600 < baseStart_1672600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672649 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 3]
def baseStart_1672649 : Nat := 118140960795 + 1672649 * 2 ^ 59
def prefixEnd_1672649 : Nat := 4983230072969 + 3 ^ 40 * 1672649 * 2
def baseEnd_1672649 : Nat := 858872903262331486795133

theorem tailTrace_1672649 : CollatzResearch.WordTrace tailWord_1672649 prefixEnd_1672649 858872903262331486795133 := by
  unfold tailWord_1672649
  simp only [CollatzResearch.WordTrace]
  refine ⟨61006520917285813551301001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40671013944857209034200667 61006520917285813551301001)
  ·
    refine ⟨45754890687964360163475751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61006520917285813551301001 45754890687964360163475751)
    ·
      refine ⟨68632336031946540245213627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45754890687964360163475751 68632336031946540245213627)
      ·
        refine ⟨102948504047919810367820441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68632336031946540245213627 102948504047919810367820441)
        ·
          refine ⟨77211378035939857775865331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102948504047919810367820441 77211378035939857775865331)
          ·
            refine ⟨115817067053909786663797997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77211378035939857775865331 115817067053909786663797997)
            ·
              refine ⟨43431400145216169998924249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115817067053909786663797997 43431400145216169998924249)
              ·
                refine ⟨32573550108912127499193187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43431400145216169998924249 32573550108912127499193187)
                ·
                  refine ⟨48860325163368191248789781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32573550108912127499193187 48860325163368191248789781)
                  ·
                    refine ⟨2290327742032883964787021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48860325163368191248789781 2290327742032883964787021)
                    ·
                      refine ⟨858872903262331486795133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2290327742032883964787021 858872903262331486795133)
                      ·
                        rfl

theorem cell23_1672649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_1672649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672649 prefixEnd_1672649 := by exact prefixLift 1672649
  have htrace : WordTrace (prefixWord ++ tailWord_1672649) baseStart_1672649 baseEnd_1672649 := by
    simpa [prefixWord, tailWord_1672649, baseEnd_1672649] using wordTrace_append hprefix tailTrace_1672649
  have hstable : (prefixWord ++ tailWord_1672649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672649).length < 2 ^ (prefixWord ++ tailWord_1672649).sum := by decide
  have hdescent : baseEnd_1672649 < baseStart_1672649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672680 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_1672680 : Nat := 118140960795 + 1672680 * 2 ^ 59
def prefixEnd_1672680 : Nat := 4983230072969 + 3 ^ 40 * 1672680 * 2
def baseEnd_1672680 : Nat := 858888821162620865507491

theorem tailTrace_1672680 : CollatzResearch.WordTrace tailWord_1672680 prefixEnd_1672680 858888821162620865507491 := by
  unfold tailWord_1672680
  simp only [CollatzResearch.WordTrace]
  refine ⟨30503825790086752922839747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40671767720115670563786329 30503825790086752922839747)
  ·
    refine ⟨45755738685130129384259621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30503825790086752922839747 45755738685130129384259621)
    ·
      refine ⟨8579201003461899259548679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45755738685130129384259621 8579201003461899259548679)
      ·
        refine ⟨12868801505192848889323019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8579201003461899259548679 12868801505192848889323019)
        ·
          refine ⟨19303202257789273333984529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12868801505192848889323019 19303202257789273333984529)
          ·
            refine ⟨14477401693341955000488397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19303202257789273333984529 14477401693341955000488397)
            ·
              refine ⟨5429025635003233125183149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14477401693341955000488397 5429025635003233125183149)
              ·
                refine ⟨2035884613126212421943681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5429025635003233125183149 2035884613126212421943681)
                ·
                  refine ⟨1526913459844659316457761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2035884613126212421943681 1526913459844659316457761)
                  ·
                    refine ⟨1145185094883494487343321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1526913459844659316457761 1145185094883494487343321)
                    ·
                      refine ⟨858888821162620865507491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145185094883494487343321 858888821162620865507491)
                      ·
                        rfl

theorem cell23_1672680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_1672680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672680 prefixEnd_1672680 := by exact prefixLift 1672680
  have htrace : WordTrace (prefixWord ++ tailWord_1672680) baseStart_1672680 baseEnd_1672680 := by
    simpa [prefixWord, tailWord_1672680, baseEnd_1672680] using wordTrace_append hprefix tailTrace_1672680
  have hstable : (prefixWord ++ tailWord_1672680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672680).length < 2 ^ (prefixWord ++ tailWord_1672680).sum := by decide
  have hdescent : baseEnd_1672680 < baseStart_1672680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672699 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 6, 5]
def baseStart_1672699 : Nat := 118140960795 + 1672699 * 2 ^ 59
def prefixEnd_1672699 : Nat := 4983230072969 + 3 ^ 40 * 1672699 * 2
def baseEnd_1672699 : Nat := 286299525765018763723301

theorem tailTrace_1672699 : CollatzResearch.WordTrace tailWord_1672699 prefixEnd_1672699 286299525765018763723301 := by
  unfold tailWord_1672699
  simp only [CollatzResearch.WordTrace]
  refine ⟨61008344567104672090621151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40672229711403114727080767 61008344567104672090621151)
  ·
    refine ⟨91512516850657008135931727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61008344567104672090621151 91512516850657008135931727)
    ·
      refine ⟨137268775275985512203897591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91512516850657008135931727 137268775275985512203897591)
      ·
        refine ⟨205903162913978268305846387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137268775275985512203897591 205903162913978268305846387)
        ·
          refine ⟨308854744370967402458769581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205903162913978268305846387 308854744370967402458769581)
          ·
            refine ⟨115820529139112775922038593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308854744370967402458769581 115820529139112775922038593)
            ·
              refine ⟨86865396854334581941528945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115820529139112775922038593 86865396854334581941528945)
              ·
                refine ⟨65149047640750936456146709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86865396854334581941528945 65149047640750936456146709)
                ·
                  refine ⟨3053861608160200146381877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65149047640750936456146709 3053861608160200146381877)
                  ·
                    refine ⟨286299525765018763723301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3053861608160200146381877 286299525765018763723301)
                    ·
                      rfl

theorem cell23_1672699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 5].length) (baseStart_1672699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672699 prefixEnd_1672699 := by exact prefixLift 1672699
  have htrace : WordTrace (prefixWord ++ tailWord_1672699) baseStart_1672699 baseEnd_1672699 := by
    simpa [prefixWord, tailWord_1672699, baseEnd_1672699] using wordTrace_append hprefix tailTrace_1672699
  have hstable : (prefixWord ++ tailWord_1672699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672699).length < 2 ^ (prefixWord ++ tailWord_1672699).sum := by decide
  have hdescent : baseEnd_1672699 < baseStart_1672699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672750 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1672750 : Nat := 118140960795 + 1672750 * 2 ^ 59
def prefixEnd_1672750 : Nat := 4983230072969 + 3 ^ 40 * 1672750 * 2
def baseEnd_1672750 : Nat := 286308254936145197210723

theorem tailTrace_1672750 : CollatzResearch.WordTrace tailWord_1672750 prefixEnd_1672750 286308254936145197210723 := by
  unfold tailWord_1672750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626275586239988475090963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40673469793279938533818469 7626275586239988475090963)
  ·
    refine ⟨11439413379359982712636445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7626275586239988475090963 11439413379359982712636445)
    ·
      refine ⟨4289780017259993517238667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11439413379359982712636445 4289780017259993517238667)
      ·
        refine ⟨6434670025889990275858001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4289780017259993517238667 6434670025889990275858001)
        ·
          refine ⟨4826002519417492706893501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6434670025889990275858001 4826002519417492706893501)
          ·
            refine ⟨1809750944781559765085063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4826002519417492706893501 1809750944781559765085063)
            ·
              refine ⟨2714626417172339647627595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809750944781559765085063 2714626417172339647627595)
              ·
                refine ⟨4071939625758509471441393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714626417172339647627595 4071939625758509471441393)
                ·
                  refine ⟨3053954719318882103581045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4071939625758509471441393 3053954719318882103581045)
                  ·
                    refine ⟨286308254936145197210723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3053954719318882103581045 286308254936145197210723)
                    ·
                      rfl

theorem cell23_1672750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1672750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672750 prefixEnd_1672750 := by exact prefixLift 1672750
  have htrace : WordTrace (prefixWord ++ tailWord_1672750) baseStart_1672750 baseEnd_1672750 := by
    simpa [prefixWord, tailWord_1672750, baseEnd_1672750] using wordTrace_append hprefix tailTrace_1672750
  have hstable : (prefixWord ++ tailWord_1672750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672750).length < 2 ^ (prefixWord ++ tailWord_1672750).sum := by decide
  have hdescent : baseEnd_1672750 < baseStart_1672750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
