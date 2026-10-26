import V185TrunkScan23Chunk0461

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2733068 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_2733068 : Nat := 118140960795 + 2733068 * 2 ^ 59
def prefixEnd_2733068 : Nat := 4983230072969 + 3 ^ 40 * 2733068 * 2
def baseEnd_2733068 : Nat := 467792515140806030860285

theorem tailTrace_2733068 : CollatzResearch.WordTrace tailWord_2733068 prefixEnd_2733068 467792515140806030860285 := by
  unfold tailWord_2733068
  simp only [CollatzResearch.WordTrace]
  refine ⟨49841589631284440848991929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66455452841712587798655905 49841589631284440848991929)
  ·
    refine ⟨37381192223463330636743947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49841589631284440848991929 37381192223463330636743947)
    ·
      refine ⟨56071788335194995955115921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37381192223463330636743947 56071788335194995955115921)
      ·
        refine ⟨42053841251396246966336941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56071788335194995955115921 42053841251396246966336941)
        ·
          refine ⟨15770190469273592612376353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42053841251396246966336941 15770190469273592612376353)
          ·
            refine ⟨11827642851955194459282265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15770190469273592612376353 11827642851955194459282265)
            ·
              refine ⟨8870732138966395844461699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11827642851955194459282265 8870732138966395844461699)
              ·
                refine ⟨13306098208449593766692549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8870732138966395844461699 13306098208449593766692549)
                ·
                  refine ⟨2494893414084298831254853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13306098208449593766692549 2494893414084298831254853)
                  ·
                    refine ⟨467792515140806030860285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2494893414084298831254853 467792515140806030860285)
                    ·
                      rfl

theorem cell23_2733068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_2733068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733068 prefixEnd_2733068 := by exact prefixLift 2733068
  have htrace : WordTrace (prefixWord ++ tailWord_2733068) baseStart_2733068 baseEnd_2733068 := by
    simpa [prefixWord, tailWord_2733068, baseEnd_2733068] using wordTrace_append hprefix tailTrace_2733068
  have hstable : (prefixWord ++ tailWord_2733068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733068).length < 2 ^ (prefixWord ++ tailWord_2733068).sum := by decide
  have hdescent : baseEnd_2733068 < baseStart_2733068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733092 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2733092 : Nat := 118140960795 + 2733092 * 2 ^ 59
def prefixEnd_2733092 : Nat := 4983230072969 + 3 ^ 40 * 2733092 * 2
def baseEnd_2733092 : Nat := 1403389868958125998680745

theorem tailTrace_2733092 : CollatzResearch.WordTrace tailWord_2733092 prefixEnd_2733092 1403389868958125998680745 := by
  unfold tailWord_2733092
  simp only [CollatzResearch.WordTrace]
  refine ⟨49842027307240966898428765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66456036409654622531238353 49842027307240966898428765)
  ·
    refine ⟨18690760240215362586910787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49842027307240966898428765 18690760240215362586910787)
    ·
      refine ⟨28036140360323043880366181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18690760240215362586910787 28036140360323043880366181)
      ·
        refine ⟨5256776317560570727568659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28036140360323043880366181 5256776317560570727568659)
        ·
          refine ⟨7885164476340856091352989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256776317560570727568659 7885164476340856091352989)
          ·
            refine ⟨2956936678627821034257371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7885164476340856091352989 2956936678627821034257371)
            ·
              refine ⟨4435405017941731551386057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2956936678627821034257371 4435405017941731551386057)
              ·
                refine ⟨3326553763456298663539543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4435405017941731551386057 3326553763456298663539543)
                ·
                  refine ⟨4989830645184447995309315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326553763456298663539543 4989830645184447995309315)
                  ·
                    refine ⟨7484745967776671992963973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4989830645184447995309315 7484745967776671992963973)
                    ·
                      refine ⟨1403389868958125998680745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7484745967776671992963973 1403389868958125998680745)
                      ·
                        rfl

theorem cell23_2733092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2733092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733092 prefixEnd_2733092 := by exact prefixLift 2733092
  have htrace : WordTrace (prefixWord ++ tailWord_2733092) baseStart_2733092 baseEnd_2733092 := by
    simpa [prefixWord, tailWord_2733092, baseEnd_2733092] using wordTrace_append hprefix tailTrace_2733092
  have hstable : (prefixWord ++ tailWord_2733092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733092).length < 2 ^ (prefixWord ++ tailWord_2733092).sum := by decide
  have hdescent : baseEnd_2733092 < baseStart_2733092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733112 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 1, 2, 3]
def baseStart_2733112 : Nat := 118140960795 + 2733112 * 2 ^ 59
def prefixEnd_2733112 : Nat := 4983230072969 + 3 ^ 40 * 2733112 * 2
def baseEnd_2733112 : Nat := 1403400138571215920430653

theorem tailTrace_2733112 : CollatzResearch.WordTrace tailWord_2733112 prefixEnd_2733112 1403400138571215920430653 := by
  unfold tailWord_2733112
  simp only [CollatzResearch.WordTrace]
  refine ⟨49842392037204738606292795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66456522716272984808390393 49842392037204738606292795)
  ·
    refine ⟨74763588055807107909439193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49842392037204738606292795 74763588055807107909439193)
    ·
      refine ⟨56072691041855330932079395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74763588055807107909439193 56072691041855330932079395)
      ·
        refine ⟨84109036562782996398119093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56072691041855330932079395 84109036562782996398119093)
        ·
          refine ⟨7885222177760905912323665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84109036562782996398119093 7885222177760905912323665)
          ·
            refine ⟨5913916633320679434242749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7885222177760905912323665 5913916633320679434242749)
            ·
              refine ⟨2217718737495254787841031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5913916633320679434242749 2217718737495254787841031)
              ·
                refine ⟨3326578106242882181761547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217718737495254787841031 3326578106242882181761547)
                ·
                  refine ⟨4989867159364323272642321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326578106242882181761547 4989867159364323272642321)
                  ·
                    refine ⟨3742400369523242454481741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4989867159364323272642321 3742400369523242454481741)
                    ·
                      refine ⟨1403400138571215920430653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3742400369523242454481741 1403400138571215920430653)
                      ·
                        rfl

theorem cell23_2733112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_2733112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733112 prefixEnd_2733112 := by exact prefixLift 2733112
  have htrace : WordTrace (prefixWord ++ tailWord_2733112) baseStart_2733112 baseEnd_2733112 := by
    simpa [prefixWord, tailWord_2733112, baseEnd_2733112] using wordTrace_append hprefix tailTrace_2733112
  have hstable : (prefixWord ++ tailWord_2733112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733112).length < 2 ^ (prefixWord ++ tailWord_2733112).sum := by decide
  have hdescent : baseEnd_2733112 < baseStart_2733112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733125 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 3]
def baseStart_2733125 : Nat := 118140960795 + 2733125 * 2 ^ 59
def prefixEnd_2733125 : Nat := 4983230072969 + 3 ^ 40 * 2733125 * 2
def baseEnd_2733125 : Nat := 1403406813819724369568093

theorem tailTrace_2733125 : CollatzResearch.WordTrace tailWord_2733125 prefixEnd_2733125 1403406813819724369568093 := by
  unfold tailWord_2733125
  simp only [CollatzResearch.WordTrace]
  refine ⟨99685258223362380432808829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66456838815574920288539219 99685258223362380432808829)
  ·
    refine ⟨37381971833760892662303311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99685258223362380432808829 37381971833760892662303311)
    ·
      refine ⟨56072957750641338993454967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37381971833760892662303311 56072957750641338993454967)
      ·
        refine ⟨84109436625962008490182451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56072957750641338993454967 84109436625962008490182451)
        ·
          refine ⟨126164154938943012735273677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84109436625962008490182451 126164154938943012735273677)
          ·
            refine ⟨47311558102103629775727629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126164154938943012735273677 47311558102103629775727629)
            ·
              refine ⟨17741834288288861165897861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47311558102103629775727629 17741834288288861165897861)
              ·
                refine ⟨3326593929054161468605849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17741834288288861165897861 3326593929054161468605849)
                ·
                  refine ⟨2494945446790621101454387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3326593929054161468605849 2494945446790621101454387)
                  ·
                    refine ⟨3742418170185931652181581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2494945446790621101454387 3742418170185931652181581)
                    ·
                      refine ⟨1403406813819724369568093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3742418170185931652181581 1403406813819724369568093)
                      ·
                        rfl

theorem cell23_2733125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_2733125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733125 prefixEnd_2733125 := by exact prefixLift 2733125
  have htrace : WordTrace (prefixWord ++ tailWord_2733125) baseStart_2733125 baseEnd_2733125 := by
    simpa [prefixWord, tailWord_2733125, baseEnd_2733125] using wordTrace_append hprefix tailTrace_2733125
  have hstable : (prefixWord ++ tailWord_2733125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733125).length < 2 ^ (prefixWord ++ tailWord_2733125).sum := by decide
  have hdescent : baseEnd_2733125 < baseStart_2733125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733148 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2733148 : Nat := 118140960795 + 2733148 * 2 ^ 59
def prefixEnd_2733148 : Nat := 4983230072969 + 3 ^ 40 * 2733148 * 2
def baseEnd_2733148 : Nat := 1403418623874777779580487

theorem tailTrace_2733148 : CollatzResearch.WordTrace tailWord_2733148 prefixEnd_2733148 1403418623874777779580487 := by
  unfold tailWord_2733148
  simp only [CollatzResearch.WordTrace]
  refine ⟨49843048551139527680448049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66457398068186036907264065 49843048551139527680448049)
  ·
    refine ⟨37382286413354645760336037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49843048551139527680448049 37382286413354645760336037)
    ·
      refine ⟨7009178702503996080063007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37382286413354645760336037 7009178702503996080063007)
      ·
        refine ⟨10513768053755994120094511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7009178702503996080063007 10513768053755994120094511)
        ·
          refine ⟨15770652080633991180141767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10513768053755994120094511 15770652080633991180141767)
          ·
            refine ⟨23655978120950986770212651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15770652080633991180141767 23655978120950986770212651)
            ·
              refine ⟨35483967181426480155318977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23655978120950986770212651 35483967181426480155318977)
              ·
                refine ⟨26612975386069860116489233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35483967181426480155318977 26612975386069860116489233)
                ·
                  refine ⟨19959731539552395087366925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26612975386069860116489233 19959731539552395087366925)
                  ·
                    refine ⟨7484899327332148157762597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19959731539552395087366925 7484899327332148157762597)
                    ·
                      refine ⟨1403418623874777779580487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7484899327332148157762597 1403418623874777779580487)
                      ·
                        rfl

theorem cell23_2733148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2733148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733148 prefixEnd_2733148 := by exact prefixLift 2733148
  have htrace : WordTrace (prefixWord ++ tailWord_2733148) baseStart_2733148 baseEnd_2733148 := by
    simpa [prefixWord, tailWord_2733148, baseEnd_2733148] using wordTrace_append hprefix tailTrace_2733148
  have hstable : (prefixWord ++ tailWord_2733148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733148).length < 2 ^ (prefixWord ++ tailWord_2733148).sum := by decide
  have hdescent : baseEnd_2733148 < baseStart_2733148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733188 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 7]
def baseStart_2733188 : Nat := 118140960795 + 2733188 * 2 ^ 59
def prefixEnd_2733188 : Nat := 4983230072969 + 3 ^ 40 * 2733188 * 2
def baseEnd_2733188 : Nat := 155937684788995291453367

theorem tailTrace_2733188 : CollatzResearch.WordTrace tailWord_2733188 prefixEnd_2733188 155937684788995291453367 := by
  unfold tailWord_2733188
  simp only [CollatzResearch.WordTrace]
  refine ⟨49843778011067071096176109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66458370681422761461568145 49843778011067071096176109)
  ·
    refine ⟨18691416754150151661066041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49843778011067071096176109 18691416754150151661066041)
    ·
      refine ⟨14018562565612613745799531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18691416754150151661066041 14018562565612613745799531)
      ·
        refine ⟨21027843848418920618699297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14018562565612613745799531 21027843848418920618699297)
        ·
          refine ⟨15770882886314190464024473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21027843848418920618699297 15770882886314190464024473)
          ·
            refine ⟨11828162164735642848018355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15770882886314190464024473 11828162164735642848018355)
            ·
              refine ⟨17742243247103464272027533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11828162164735642848018355 17742243247103464272027533)
              ·
                refine ⟨6653341217663799102010325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17742243247103464272027533 6653341217663799102010325)
                ·
                  refine ⟨155937684788995291453367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6653341217663799102010325 155937684788995291453367)
                  ·
                    rfl

theorem cell23_2733188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_2733188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733188 prefixEnd_2733188 := by exact prefixLift 2733188
  have htrace : WordTrace (prefixWord ++ tailWord_2733188) baseStart_2733188 baseEnd_2733188 := by
    simpa [prefixWord, tailWord_2733188, baseEnd_2733188] using wordTrace_append hprefix tailTrace_2733188
  have hstable : (prefixWord ++ tailWord_2733188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733188).length < 2 ^ (prefixWord ++ tailWord_2733188).sum := by decide
  have hdescent : baseEnd_2733188 < baseStart_2733188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733255 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_2733255 : Nat := 118140960795 + 2733255 * 2 ^ 59
def prefixEnd_2733255 : Nat := 4983230072969 + 3 ^ 40 * 2733255 * 2
def baseEnd_2733255 : Nat := 1403473566304808860942495

theorem tailTrace_2733255 : CollatzResearch.WordTrace tailWord_2733255 prefixEnd_2733255 1403473566304808860942495 := by
  unfold tailWord_2733255
  simp only [CollatzResearch.WordTrace]
  refine ⟨99689999712891412635041219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66459999808594275090027479 99689999712891412635041219)
  ·
    refine ⟨149534999569337118952561829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99689999712891412635041219 149534999569337118952561829)
    ·
      refine ⟨28037812419250709803605343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149534999569337118952561829 28037812419250709803605343)
      ·
        refine ⟨42056718628876064705408015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28037812419250709803605343 42056718628876064705408015)
        ·
          refine ⟨63085077943314097058112023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42056718628876064705408015 63085077943314097058112023)
          ·
            refine ⟨94627616914971145587168035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63085077943314097058112023 94627616914971145587168035)
            ·
              refine ⟨141941425372456718380752053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94627616914971145587168035 141941425372456718380752053)
              ·
                refine ⟨13307008628667817348195505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141941425372456718380752053 13307008628667817348195505)
                ·
                  refine ⟨9980256471500863011146629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13307008628667817348195505 9980256471500863011146629)
                  ·
                    refine ⟨1871298088406411814589993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9980256471500863011146629 1871298088406411814589993)
                    ·
                      refine ⟨1403473566304808860942495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1871298088406411814589993 1403473566304808860942495)
                      ·
                        rfl

theorem cell23_2733255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_2733255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733255 prefixEnd_2733255 := by exact prefixLift 2733255
  have htrace : WordTrace (prefixWord ++ tailWord_2733255) baseStart_2733255 baseEnd_2733255 := by
    simpa [prefixWord, tailWord_2733255, baseEnd_2733255] using wordTrace_append hprefix tailTrace_2733255
  have hstable : (prefixWord ++ tailWord_2733255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733255).length < 2 ^ (prefixWord ++ tailWord_2733255).sum := by decide
  have hdescent : baseEnd_2733255 < baseStart_2733255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733272 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_2733272 : Nat := 118140960795 + 2733272 * 2 ^ 59
def prefixEnd_2733272 : Nat := 4983230072969 + 3 ^ 40 * 2733272 * 2
def baseEnd_2733272 : Nat := 1403482295475935294429917

theorem tailTrace_2733272 : CollatzResearch.WordTrace tailWord_2733272 prefixEnd_2733272 1403482295475935294429917 := by
  unfold tailWord_2733272
  simp only [CollatzResearch.WordTrace]
  refine ⟨49845309876914912269205035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66460413169219883025606713 49845309876914912269205035)
  ·
    refine ⟨74767964815372368403807553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49845309876914912269205035 74767964815372368403807553)
    ·
      refine ⟨56075973611529276302855665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74767964815372368403807553 56075973611529276302855665)
      ·
        refine ⟨42056980208646957227141749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56075973611529276302855665 42056980208646957227141749)
        ·
          refine ⟨3942841894560652240044539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42056980208646957227141749 3942841894560652240044539)
          ·
            refine ⟨5914262841840978360066809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942841894560652240044539 5914262841840978360066809)
            ·
              refine ⟨4435697131380733770050107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5914262841840978360066809 4435697131380733770050107)
              ·
                refine ⟨6653545697071100655075161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435697131380733770050107 6653545697071100655075161)
                ·
                  refine ⟨4990159272803325491306371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6653545697071100655075161 4990159272803325491306371)
                  ·
                    refine ⟨7485238909204988236959557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4990159272803325491306371 7485238909204988236959557)
                    ·
                      refine ⟨1403482295475935294429917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7485238909204988236959557 1403482295475935294429917)
                      ·
                        rfl

theorem cell23_2733272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_2733272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733272 prefixEnd_2733272 := by exact prefixLift 2733272
  have htrace : WordTrace (prefixWord ++ tailWord_2733272) baseStart_2733272 baseEnd_2733272 := by
    simpa [prefixWord, tailWord_2733272, baseEnd_2733272] using wordTrace_append hprefix tailTrace_2733272
  have hstable : (prefixWord ++ tailWord_2733272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733272).length < 2 ^ (prefixWord ++ tailWord_2733272).sum := by decide
  have hdescent : baseEnd_2733272 < baseStart_2733272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733299 : List Nat := [1, 1, 1, 2, 2, 5, 4, 2, 1, 4]
def baseStart_2733299 : Nat := 118140960795 + 2733299 * 2 ^ 59
def prefixEnd_2733299 : Nat := 4983230072969 + 3 ^ 40 * 2733299 * 2
def baseEnd_2733299 : Nat := 467832053151202229597431

theorem tailTrace_2733299 : CollatzResearch.WordTrace tailWord_2733299 prefixEnd_2733299 467832053151202229597431 := by
  unfold tailWord_2733299
  simp only [CollatzResearch.WordTrace]
  refine ⟨99691604524732008149642951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66461069683154672099761967 99691604524732008149642951)
  ·
    refine ⟨149537406787098012224464427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99691604524732008149642951 149537406787098012224464427)
    ·
      refine ⟨224306110180647018336696641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149537406787098012224464427 224306110180647018336696641)
      ·
        refine ⟨168229582635485263752522481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224306110180647018336696641 168229582635485263752522481)
        ·
          refine ⟨126172186976613947814391861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168229582635485263752522481 126172186976613947814391861)
          ·
            refine ⟨11828642529057557607599237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126172186976613947814391861 11828642529057557607599237)
            ·
              refine ⟨2217870474198292051424857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11828642529057557607599237 2217870474198292051424857)
              ·
                refine ⟨1663402855648719038568643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217870474198292051424857 1663402855648719038568643)
                ·
                  refine ⟨2495104283473078557852965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663402855648719038568643 2495104283473078557852965)
                  ·
                    refine ⟨467832053151202229597431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495104283473078557852965 467832053151202229597431)
                    ·
                      rfl

theorem cell23_2733299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 4].length) (baseStart_2733299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733299 prefixEnd_2733299 := by exact prefixLift 2733299
  have htrace : WordTrace (prefixWord ++ tailWord_2733299) baseStart_2733299 baseEnd_2733299 := by
    simpa [prefixWord, tailWord_2733299, baseEnd_2733299] using wordTrace_append hprefix tailTrace_2733299
  have hstable : (prefixWord ++ tailWord_2733299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733299).length < 2 ^ (prefixWord ++ tailWord_2733299).sum := by decide
  have hdescent : baseEnd_2733299 < baseStart_2733299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733365 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2733365 : Nat := 118140960795 + 2733365 * 2 ^ 59
def prefixEnd_2733365 : Nat := 4983230072969 + 3 ^ 40 * 2733365 * 2
def baseEnd_2733365 : Nat := 1403530049176803430566989

theorem tailTrace_2733365 : CollatzResearch.WordTrace tailWord_2733365 prefixEnd_2733365 1403530049176803430566989 := by
  unfold tailWord_2733365
  simp only [CollatzResearch.WordTrace]
  refine ⟨99694011742492901421545549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66462674494995267614363699 99694011742492901421545549)
  ·
    refine ⟨37385254403434838033079581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99694011742492901421545549 37385254403434838033079581)
    ·
      refine ⟨14019470401288064262404843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37385254403434838033079581 14019470401288064262404843)
      ·
        refine ⟨21029205601932096393607265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14019470401288064262404843 21029205601932096393607265)
        ·
          refine ⟨15771904201449072295205449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21029205601932096393607265 15771904201449072295205449)
          ·
            refine ⟨11828928151086804221404087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15771904201449072295205449 11828928151086804221404087)
            ·
              refine ⟨17743392226630206332106131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11828928151086804221404087 17743392226630206332106131)
              ·
                refine ⟨26615088339945309498159197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17743392226630206332106131 26615088339945309498159197)
                ·
                  refine ⟨9980658127479491061809699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26615088339945309498159197 9980658127479491061809699)
                  ·
                    refine ⟨14970987191219236592714549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9980658127479491061809699 14970987191219236592714549)
                    ·
                      refine ⟨1403530049176803430566989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14970987191219236592714549 1403530049176803430566989)
                      ·
                        rfl

theorem cell23_2733365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2733365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733365 prefixEnd_2733365 := by exact prefixLift 2733365
  have htrace : WordTrace (prefixWord ++ tailWord_2733365) baseStart_2733365 baseEnd_2733365 := by
    simpa [prefixWord, tailWord_2733365, baseEnd_2733365] using wordTrace_append hprefix tailTrace_2733365
  have hstable : (prefixWord ++ tailWord_2733365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733365).length < 2 ^ (prefixWord ++ tailWord_2733365).sum := by decide
  have hdescent : baseEnd_2733365 < baseStart_2733365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733368 : List Nat := [2, 1, 2, 1, 3, 1, 1, 12]
def baseStart_2733368 : Nat := 118140960795 + 2733368 * 2 ^ 59
def prefixEnd_2733368 : Nat := 4983230072969 + 3 ^ 40 * 2733368 * 2
def baseEnd_2733368 : Nat := 51982651467361737734425

theorem tailTrace_2733368 : CollatzResearch.WordTrace tailWord_2733368 prefixEnd_2733368 51982651467361737734425 := by
  unfold tailWord_2733368
  simp only [CollatzResearch.WordTrace]
  refine ⟨49847060580741016466952379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66462747440988021955936505 49847060580741016466952379)
  ·
    refine ⟨74770590871111524700428569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49847060580741016466952379 74770590871111524700428569)
    ·
      refine ⟨56077943153333643525321427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74770590871111524700428569 56077943153333643525321427)
      ·
        refine ⟨84116914730000465287982141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56077943153333643525321427 84116914730000465287982141)
        ·
          refine ⟨31543843023750174482993303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84116914730000465287982141 31543843023750174482993303)
          ·
            refine ⟨47315764535625261724489955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31543843023750174482993303 47315764535625261724489955)
            ·
              refine ⟨70973646803437892586734933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47315764535625261724489955 70973646803437892586734933)
              ·
                refine ⟨51982651467361737734425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 70973646803437892586734933 51982651467361737734425)
                ·
                  rfl

theorem cell23_2733368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 12].length) (baseStart_2733368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733368 prefixEnd_2733368 := by exact prefixLift 2733368
  have htrace : WordTrace (prefixWord ++ tailWord_2733368) baseStart_2733368 baseEnd_2733368 := by
    simpa [prefixWord, tailWord_2733368, baseEnd_2733368] using wordTrace_append hprefix tailTrace_2733368
  have hstable : (prefixWord ++ tailWord_2733368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733368).length < 2 ^ (prefixWord ++ tailWord_2733368).sum := by decide
  have hdescent : baseEnd_2733368 < baseStart_2733368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733372 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_2733372 : Nat := 118140960795 + 2733372 * 2 ^ 59
def prefixEnd_2733372 : Nat := 4983230072969 + 3 ^ 40 * 2733372 * 2
def baseEnd_2733372 : Nat := 467844547847128301059819

theorem tailTrace_2733372 : CollatzResearch.WordTrace tailWord_2733372 prefixEnd_2733372 467844547847128301059819 := by
  unfold tailWord_2733372
  simp only [CollatzResearch.WordTrace]
  refine ⟨49847133526733770808525185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66462844702311694411366913 49847133526733770808525185)
  ·
    refine ⟨37385350145050328106393889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49847133526733770808525185 37385350145050328106393889)
    ·
      refine ⟨28039012608787746079795417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37385350145050328106393889 28039012608787746079795417)
      ·
        refine ⟨21029259456590809559846563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28039012608787746079795417 21029259456590809559846563)
        ·
          refine ⟨31543889184886214339769845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21029259456590809559846563 31543889184886214339769845)
          ·
            refine ⟨2957239611083082594353423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31543889184886214339769845 2957239611083082594353423)
            ·
              refine ⟨4435859416624623891530135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2957239611083082594353423 4435859416624623891530135)
              ·
                refine ⟨6653789124936935837295203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435859416624623891530135 6653789124936935837295203)
                ·
                  refine ⟨9980683687405403755942805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6653789124936935837295203 9980683687405403755942805)
                  ·
                    refine ⟨467844547847128301059819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9980683687405403755942805 467844547847128301059819)
                    ·
                      rfl

theorem cell23_2733372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_2733372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733372 prefixEnd_2733372 := by exact prefixLift 2733372
  have htrace : WordTrace (prefixWord ++ tailWord_2733372) baseStart_2733372 baseEnd_2733372 := by
    simpa [prefixWord, tailWord_2733372, baseEnd_2733372] using wordTrace_append hprefix tailTrace_2733372
  have hstable : (prefixWord ++ tailWord_2733372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733372).length < 2 ^ (prefixWord ++ tailWord_2733372).sum := by decide
  have hdescent : baseEnd_2733372 < baseStart_2733372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733375 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_2733375 : Nat := 118140960795 + 2733375 * 2 ^ 59
def prefixEnd_2733375 : Nat := 4983230072969 + 3 ^ 40 * 2733375 * 2
def baseEnd_2733375 : Nat := 1403535183983348391441943

theorem tailTrace_2733375 : CollatzResearch.WordTrace tailWord_2733375 prefixEnd_2733375 1403535183983348391441943 := by
  unfold tailWord_2733375
  simp only [CollatzResearch.WordTrace]
  refine ⟨99694376472456673129409579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66462917648304448752939719 99694376472456673129409579)
  ·
    refine ⟨149541564708685009694114369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99694376472456673129409579 149541564708685009694114369)
    ·
      refine ⟨112156173531513757270585777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149541564708685009694114369 112156173531513757270585777)
      ·
        refine ⟨84117130148635317952939333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112156173531513757270585777 84117130148635317952939333)
        ·
          refine ⟨15771961902869122116176125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84117130148635317952939333 15771961902869122116176125)
          ·
            refine ⟨5914485713575920793566047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15771961902869122116176125 5914485713575920793566047)
            ·
              refine ⟨8871728570363881190349071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5914485713575920793566047 8871728570363881190349071)
              ·
                refine ⟨13307592855545821785523607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8871728570363881190349071 13307592855545821785523607)
                ·
                  refine ⟨19961389283318732678285411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13307592855545821785523607 19961389283318732678285411)
                  ·
                    refine ⟨29942083924978099017428117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19961389283318732678285411 29942083924978099017428117)
                    ·
                      refine ⟨1403535183983348391441943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29942083924978099017428117 1403535183983348391441943)
                      ·
                        rfl

theorem cell23_2733375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_2733375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733375 prefixEnd_2733375 := by exact prefixLift 2733375
  have htrace : WordTrace (prefixWord ++ tailWord_2733375) baseStart_2733375 baseEnd_2733375 := by
    simpa [prefixWord, tailWord_2733375, baseEnd_2733375] using wordTrace_append hprefix tailTrace_2733375
  have hstable : (prefixWord ++ tailWord_2733375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733375).length < 2 ^ (prefixWord ++ tailWord_2733375).sum := by decide
  have hdescent : baseEnd_2733375 < baseStart_2733375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733385 : List Nat := [1, 2, 1, 1, 2, 3, 6, 7]
def baseStart_2733385 : Nat := 118140960795 + 2733385 * 2 ^ 59
def prefixEnd_2733385 : Nat := 4983230072969 + 3 ^ 40 * 2733385 * 2
def baseEnd_2733385 : Nat := 51982974769996050085811

theorem tailTrace_2733385 : CollatzResearch.WordTrace tailWord_2733385 prefixEnd_2733385 51982974769996050085811 := by
  unfold tailWord_2733385
  simp only [CollatzResearch.WordTrace]
  refine ⟨99694741202420444837273609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66463160801613629891515739 99694741202420444837273609)
  ·
    refine ⟨74771055901815333627955207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99694741202420444837273609 74771055901815333627955207)
    ·
      refine ⟨112156583852723000441932811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74771055901815333627955207 112156583852723000441932811)
      ·
        refine ⟨168234875779084500662899217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112156583852723000441932811 168234875779084500662899217)
        ·
          refine ⟨126176156834313375497174413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168234875779084500662899217 126176156834313375497174413)
          ·
            refine ⟨47316058812867515811440405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126176156834313375497174413 47316058812867515811440405)
            ·
              refine ⟨2217940256853164803661269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47316058812867515811440405 2217940256853164803661269)
              ·
                refine ⟨51982974769996050085811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2217940256853164803661269 51982974769996050085811)
                ·
                  rfl

theorem cell23_2733385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 7].length) (baseStart_2733385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733385 prefixEnd_2733385 := by exact prefixLift 2733385
  have htrace : WordTrace (prefixWord ++ tailWord_2733385) baseStart_2733385 baseEnd_2733385 := by
    simpa [prefixWord, tailWord_2733385, baseEnd_2733385] using wordTrace_append hprefix tailTrace_2733385
  have hstable : (prefixWord ++ tailWord_2733385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733385).length < 2 ^ (prefixWord ++ tailWord_2733385).sum := by decide
  have hdescent : baseEnd_2733385 < baseStart_2733385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733395 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 3]
def baseStart_2733395 : Nat := 118140960795 + 2733395 * 2 ^ 59
def prefixEnd_2733395 : Nat := 4983230072969 + 3 ^ 40 * 2733395 * 2
def baseEnd_2733395 : Nat := 1403545453596438313191851

theorem tailTrace_2733395 : CollatzResearch.WordTrace tailWord_2733395 prefixEnd_2733395 1403545453596438313191851 := by
  unfold tailWord_2733395
  simp only [CollatzResearch.WordTrace]
  refine ⟨99695105932384216545137639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66463403954922811030091759 99695105932384216545137639)
  ·
    refine ⟨149542658898576324817706459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99695105932384216545137639 149542658898576324817706459)
    ·
      refine ⟨224313988347864487226559689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149542658898576324817706459 224313988347864487226559689)
      ·
        refine ⟨168235491260898365419919767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224313988347864487226559689 168235491260898365419919767)
        ·
          refine ⟨252353236891347548129879651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168235491260898365419919767 252353236891347548129879651)
          ·
            refine ⟨378529855337021322194819477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252353236891347548129879651 378529855337021322194819477)
            ·
              refine ⟨17743586968922874477882163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 378529855337021322194819477 17743586968922874477882163)
              ·
                refine ⟨26615380453384311716823245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17743586968922874477882163 26615380453384311716823245)
                ·
                  refine ⟨9980767670019116893808717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26615380453384311716823245 9980767670019116893808717)
                  ·
                    refine ⟨3742787876257168835178269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9980767670019116893808717 3742787876257168835178269)
                    ·
                      refine ⟨1403545453596438313191851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3742787876257168835178269 1403545453596438313191851)
                      ·
                        rfl

theorem cell23_2733395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_2733395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733395 prefixEnd_2733395 := by exact prefixLift 2733395
  have htrace : WordTrace (prefixWord ++ tailWord_2733395) baseStart_2733395 baseEnd_2733395 := by
    simpa [prefixWord, tailWord_2733395, baseEnd_2733395] using wordTrace_append hprefix tailTrace_2733395
  have hstable : (prefixWord ++ tailWord_2733395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733395).length < 2 ^ (prefixWord ++ tailWord_2733395).sum := by decide
  have hdescent : baseEnd_2733395 < baseStart_2733395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733413 : List Nat := [1, 3, 1, 3, 1, 2, 5, 2, 1, 2, 2]
def baseStart_2733413 : Nat := 118140960795 + 2733413 * 2 ^ 59
def prefixEnd_2733413 : Nat := 4983230072969 + 3 ^ 40 * 2733413 * 2
def baseEnd_2733413 : Nat := 1403554696248219242766769

theorem tailTrace_2733413 : CollatzResearch.WordTrace tailWord_2733413 prefixEnd_2733413 1403554696248219242766769 := by
  unfold tailWord_2733413
  simp only [CollatzResearch.WordTrace]
  refine ⟨99695762446319005619292893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66463841630879337079528595 99695762446319005619292893)
  ·
    refine ⟨37385910917369627107234835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99695762446319005619292893 37385910917369627107234835)
    ·
      refine ⟨56078866376054440660852253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37385910917369627107234835 56078866376054440660852253)
      ·
        refine ⟨21029574891020415247819595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56078866376054440660852253 21029574891020415247819595)
        ·
          refine ⟨31544362336530622871729393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21029574891020415247819595 31544362336530622871729393)
          ·
            refine ⟨23658271752397967153797045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31544362336530622871729393 23658271752397967153797045)
            ·
              refine ⟨2217962976787309420668473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23658271752397967153797045 2217962976787309420668473)
              ·
                refine ⟨1663472232590482065501355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217962976787309420668473 1663472232590482065501355)
                ·
                  refine ⟨2495208348885723098252033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663472232590482065501355 2495208348885723098252033)
                  ·
                    refine ⟨1871406261664292323689025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2495208348885723098252033 1871406261664292323689025)
                    ·
                      refine ⟨1403554696248219242766769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1871406261664292323689025 1403554696248219242766769)
                      ·
                        rfl

theorem cell23_2733413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_2733413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733413 prefixEnd_2733413 := by exact prefixLift 2733413
  have htrace : WordTrace (prefixWord ++ tailWord_2733413) baseStart_2733413 baseEnd_2733413 := by
    simpa [prefixWord, tailWord_2733413, baseEnd_2733413] using wordTrace_append hprefix tailTrace_2733413
  have hstable : (prefixWord ++ tailWord_2733413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733413).length < 2 ^ (prefixWord ++ tailWord_2733413).sum := by decide
  have hdescent : baseEnd_2733413 < baseStart_2733413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733475 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 7]
def baseStart_2733475 : Nat := 118140960795 + 2733475 * 2 ^ 59
def prefixEnd_2733475 : Nat := 4983230072969 + 3 ^ 40 * 2733475 * 2
def baseEnd_2733475 : Nat := 155954059116533111132387

theorem tailTrace_2733475 : CollatzResearch.WordTrace tailWord_2733475 prefixEnd_2733475 155954059116533111132387 := by
  unfold tailWord_2733475
  simp only [CollatzResearch.WordTrace]
  refine ⟨99698023772094390208049879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66465349181396260138699919 99698023772094390208049879)
  ·
    refine ⟨149547035658141585312074819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99698023772094390208049879 149547035658141585312074819)
    ·
      refine ⟨224320553487212377968112229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149547035658141585312074819 224320553487212377968112229)
      ·
        refine ⟨42060103778852320869021043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224320553487212377968112229 42060103778852320869021043)
        ·
          refine ⟨63090155668278481303531565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42060103778852320869021043 63090155668278481303531565)
          ·
            refine ⟨23658808375604430488824337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63090155668278481303531565 23658808375604430488824337)
            ·
              refine ⟨17744106281703322866618253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23658808375604430488824337 17744106281703322866618253)
              ·
                refine ⟨6654039855638746074981845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17744106281703322866618253 6654039855638746074981845)
                ·
                  refine ⟨155954059116533111132387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6654039855638746074981845 155954059116533111132387)
                  ·
                    rfl

theorem cell23_2733475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 7].length) (baseStart_2733475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733475 prefixEnd_2733475 := by exact prefixLift 2733475
  have htrace : WordTrace (prefixWord ++ tailWord_2733475) baseStart_2733475 baseEnd_2733475 := by
    simpa [prefixWord, tailWord_2733475, baseEnd_2733475] using wordTrace_append hprefix tailTrace_2733475
  have hstable : (prefixWord ++ tailWord_2733475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733475).length < 2 ^ (prefixWord ++ tailWord_2733475).sum := by decide
  have hdescent : baseEnd_2733475 < baseStart_2733475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733502 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_2733502 : Nat := 118140960795 + 2733502 * 2 ^ 59
def prefixEnd_2733502 : Nat := 4983230072969 + 3 ^ 40 * 2733502 * 2
def baseEnd_2733502 : Nat := 1403600396026469394553859

theorem tailTrace_2733502 : CollatzResearch.WordTrace tailWord_2733502 prefixEnd_2733502 1403600396026469394553859 := by
  unfold tailWord_2733502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12462376067874571727410345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66466005695331049212855173 12462376067874571727410345)
  ·
    refine ⟨9346782050905928795557759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12462376067874571727410345 9346782050905928795557759)
    ·
      refine ⟨14020173076358893193336639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9346782050905928795557759 14020173076358893193336639)
      ·
        refine ⟨21030259614538339790004959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14020173076358893193336639 21030259614538339790004959)
        ·
          refine ⟨31545389421807509685007439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21030259614538339790004959 31545389421807509685007439)
          ·
            refine ⟨47318084132711264527511159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31545389421807509685007439 47318084132711264527511159)
            ·
              refine ⟨70977126199066896791266739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47318084132711264527511159 70977126199066896791266739)
              ·
                refine ⟨106465689298600345186900109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70977126199066896791266739 106465689298600345186900109)
                ·
                  refine ⟨39924633486975129445087541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106465689298600345186900109 39924633486975129445087541)
                  ·
                    refine ⟨3742934389403918385476957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39924633486975129445087541 3742934389403918385476957)
                    ·
                      refine ⟨1403600396026469394553859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3742934389403918385476957 1403600396026469394553859)
                      ·
                        rfl

theorem cell23_2733502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_2733502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733502 prefixEnd_2733502 := by exact prefixLift 2733502
  have htrace : WordTrace (prefixWord ++ tailWord_2733502) baseStart_2733502 baseEnd_2733502 := by
    simpa [prefixWord, tailWord_2733502, baseEnd_2733502] using wordTrace_append hprefix tailTrace_2733502
  have hstable : (prefixWord ++ tailWord_2733502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733502).length < 2 ^ (prefixWord ++ tailWord_2733502).sum := by decide
  have hdescent : baseEnd_2733502 < baseStart_2733502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733515 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 5]
def baseStart_2733515 : Nat := 118140960795 + 2733515 * 2 ^ 59
def prefixEnd_2733515 : Nat := 4983230072969 + 3 ^ 40 * 2733515 * 2
def baseEnd_2733515 : Nat := 1403607071274977843691299

theorem tailTrace_2733515 : CollatzResearch.WordTrace tailWord_2733515 prefixEnd_2733515 1403607071274977843691299 := by
  unfold tailWord_2733515
  simp only [CollatzResearch.WordTrace]
  refine ⟨99699482691949477039505999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66466321794632984693003999 99699482691949477039505999)
  ·
    refine ⟨149549224037924215559258999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99699482691949477039505999 149549224037924215559258999)
    ·
      refine ⟨224323836056886323338888499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149549224037924215559258999 224323836056886323338888499)
      ·
        refine ⟨336485754085329485008332749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224323836056886323338888499 336485754085329485008332749)
        ·
          refine ⟨126182157781998556878124781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336485754085329485008332749 126182157781998556878124781)
          ·
            refine ⟨47318309168249458829296793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126182157781998556878124781 47318309168249458829296793)
            ·
              refine ⟨35488731876187094121972595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47318309168249458829296793 35488731876187094121972595)
              ·
                refine ⟨53233097814280641182958893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35488731876187094121972595 53233097814280641182958893)
                ·
                  refine ⟨19962411680355240443609585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53233097814280641182958893 19962411680355240443609585)
                  ·
                    refine ⟨14971808760266430332707189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19962411680355240443609585 14971808760266430332707189)
                    ·
                      refine ⟨1403607071274977843691299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14971808760266430332707189 1403607071274977843691299)
                      ·
                        rfl

theorem cell23_2733515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_2733515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733515 prefixEnd_2733515 := by exact prefixLift 2733515
  have htrace : WordTrace (prefixWord ++ tailWord_2733515) baseStart_2733515 baseEnd_2733515 := by
    simpa [prefixWord, tailWord_2733515, baseEnd_2733515] using wordTrace_append hprefix tailTrace_2733515
  have hstable : (prefixWord ++ tailWord_2733515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733515).length < 2 ^ (prefixWord ++ tailWord_2733515).sum := by decide
  have hdescent : baseEnd_2733515 < baseStart_2733515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733526 : List Nat := [5, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2733526 : Nat := 118140960795 + 2733526 * 2 ^ 59
def prefixEnd_2733526 : Nat := 4983230072969 + 3 ^ 40 * 2733526 * 2
def baseEnd_2733526 : Nat := 155956968840241922294861

theorem tailTrace_2733526 : CollatzResearch.WordTrace tailWord_2733526 prefixEnd_2733526 155956968840241922294861 := by
  unfold tailWord_2733526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231242743431851619884777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66466589263273083945437621 6231242743431851619884777)
  ·
    refine ⟨4673432057573888714913583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6231242743431851619884777 4673432057573888714913583)
    ·
      refine ⟨7010148086360833072370375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4673432057573888714913583 7010148086360833072370375)
      ·
        refine ⟨10515222129541249608555563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010148086360833072370375 10515222129541249608555563)
        ·
          refine ⟨15772833194311874412833345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10515222129541249608555563 15772833194311874412833345)
          ·
            refine ⟨11829624895733905809625009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15772833194311874412833345 11829624895733905809625009)
            ·
              refine ⟨8872218671800429357218757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11829624895733905809625009 8872218671800429357218757)
              ·
                refine ⟨1663541000962580504478517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8872218671800429357218757 1663541000962580504478517)
                ·
                  refine ⟨155956968840241922294861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1663541000962580504478517 155956968840241922294861)
                  ·
                    rfl

theorem cell23_2733526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2733526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733526 prefixEnd_2733526 := by exact prefixLift 2733526
  have htrace : WordTrace (prefixWord ++ tailWord_2733526) baseStart_2733526 baseEnd_2733526 := by
    simpa [prefixWord, tailWord_2733526, baseEnd_2733526] using wordTrace_append hprefix tailTrace_2733526
  have hstable : (prefixWord ++ tailWord_2733526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733526).length < 2 ^ (prefixWord ++ tailWord_2733526).sum := by decide
  have hdescent : baseEnd_2733526 < baseStart_2733526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733545 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_2733545 : Nat := 118140960795 + 2733545 * 2 ^ 59
def prefixEnd_2733545 : Nat := 4983230072969 + 3 ^ 40 * 2733545 * 2
def baseEnd_2733545 : Nat := 1403622475694612726316161

theorem tailTrace_2733545 : CollatzResearch.WordTrace tailWord_2733545 prefixEnd_2733545 1403622475694612726316161 := by
  unfold tailWord_2733545
  simp only [CollatzResearch.WordTrace]
  refine ⟨99700576881840792163098089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66467051254560528108732059 99700576881840792163098089)
  ·
    refine ⟨74775432661380594122323567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99700576881840792163098089 74775432661380594122323567)
    ·
      refine ⟨112163148992070891183485351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74775432661380594122323567 112163148992070891183485351)
      ·
        refine ⟨168244723488106336775228027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112163148992070891183485351 168244723488106336775228027)
        ·
          refine ⟨252367085232159505162842041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168244723488106336775228027 252367085232159505162842041)
          ·
            refine ⟨189275313924119628872131531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252367085232159505162842041 189275313924119628872131531)
            ·
              refine ⟨283912970886179443308197297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189275313924119628872131531 283912970886179443308197297)
              ·
                refine ⟨212934728164634582481147973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283912970886179443308197297 212934728164634582481147973)
                ·
                  refine ⟨39925261530868984215215245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212934728164634582481147973 39925261530868984215215245)
                  ·
                    refine ⟨14971973074075869080705717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39925261530868984215215245 14971973074075869080705717)
                    ·
                      refine ⟨1403622475694612726316161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14971973074075869080705717 1403622475694612726316161)
                      ·
                        rfl

theorem cell23_2733545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_2733545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733545 prefixEnd_2733545 := by exact prefixLift 2733545
  have htrace : WordTrace (prefixWord ++ tailWord_2733545) baseStart_2733545 baseEnd_2733545 := by
    simpa [prefixWord, tailWord_2733545, baseEnd_2733545] using wordTrace_append hprefix tailTrace_2733545
  have hstable : (prefixWord ++ tailWord_2733545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733545).length < 2 ^ (prefixWord ++ tailWord_2733545).sum := by decide
  have hdescent : baseEnd_2733545 < baseStart_2733545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733555 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 6]
def baseStart_2733555 : Nat := 118140960795 + 2733555 * 2 ^ 59
def prefixEnd_2733555 : Nat := 4983230072969 + 3 ^ 40 * 2733555 * 2
def baseEnd_2733555 : Nat := 1403627610501157687191115

theorem tailTrace_2733555 : CollatzResearch.WordTrace tailWord_2733555 prefixEnd_2733555 1403627610501157687191115 := by
  unfold tailWord_2733555
  simp only [CollatzResearch.WordTrace]
  refine ⟨99700941611804563870962119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66467294407869709247308079 99700941611804563870962119)
  ·
    refine ⟨149551412417706845806443179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99700941611804563870962119 149551412417706845806443179)
    ·
      refine ⟨224327118626560268709664769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149551412417706845806443179 224327118626560268709664769)
      ·
        refine ⟨168245338969920201532248577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224327118626560268709664769 168245338969920201532248577)
        ·
          refine ⟨126184004227440151149186433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168245338969920201532248577 126184004227440151149186433)
          ·
            refine ⟨94638003170580113361889825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126184004227440151149186433 94638003170580113361889825)
            ·
              refine ⟨70978502377935085021417369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94638003170580113361889825 70978502377935085021417369)
              ·
                refine ⟨53233876783451313766063027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70978502377935085021417369 53233876783451313766063027)
                ·
                  refine ⟨79850815175176970649094541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53233876783451313766063027 79850815175176970649094541)
                  ·
                    refine ⟨29944055690691363993410453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79850815175176970649094541 29944055690691363993410453)
                    ·
                      refine ⟨1403627610501157687191115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29944055690691363993410453 1403627610501157687191115)
                      ·
                        rfl

theorem cell23_2733555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_2733555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733555 prefixEnd_2733555 := by exact prefixLift 2733555
  have htrace : WordTrace (prefixWord ++ tailWord_2733555) baseStart_2733555 baseEnd_2733555 := by
    simpa [prefixWord, tailWord_2733555, baseEnd_2733555] using wordTrace_append hprefix tailTrace_2733555
  have hstable : (prefixWord ++ tailWord_2733555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733555).length < 2 ^ (prefixWord ++ tailWord_2733555).sum := by decide
  have hdescent : baseEnd_2733555 < baseStart_2733555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733562 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_2733562 : Nat := 118140960795 + 2733562 * 2 ^ 59
def prefixEnd_2733562 : Nat := 4983230072969 + 3 ^ 40 * 2733562 * 2
def baseEnd_2733562 : Nat := 1403631204865739159803583

theorem tailTrace_2733562 : CollatzResearch.WordTrace tailWord_2733562 prefixEnd_2733562 1403631204865739159803583 := by
  unfold tailWord_2733562
  simp only [CollatzResearch.WordTrace]
  refine ⟨24925299230694801016616735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66467464615186136044311293 24925299230694801016616735)
  ·
    refine ⟨37387948846042201524925103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24925299230694801016616735 37387948846042201524925103)
    ·
      refine ⟨56081923269063302287387655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37387948846042201524925103 56081923269063302287387655)
      ·
        refine ⟨84122884903594953431081483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56081923269063302287387655 84122884903594953431081483)
        ·
          refine ⟨126184327355392430146622225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84122884903594953431081483 126184327355392430146622225)
          ·
            refine ⟨94638245516544322609966669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126184327355392430146622225 94638245516544322609966669)
            ·
              refine ⟨35489342068704120978737501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94638245516544322609966669 35489342068704120978737501)
              ·
                refine ⟨13308503275764045367026563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35489342068704120978737501 13308503275764045367026563)
                ·
                  refine ⟨19962754913646068050539845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13308503275764045367026563 19962754913646068050539845)
                  ·
                    refine ⟨3743016546308637759476221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19962754913646068050539845 3743016546308637759476221)
                    ·
                      refine ⟨1403631204865739159803583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3743016546308637759476221 1403631204865739159803583)
                      ·
                        rfl

theorem cell23_2733562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_2733562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733562 prefixEnd_2733562 := by exact prefixLift 2733562
  have htrace : WordTrace (prefixWord ++ tailWord_2733562) baseStart_2733562 baseEnd_2733562 := by
    simpa [prefixWord, tailWord_2733562, baseEnd_2733562] using wordTrace_append hprefix tailTrace_2733562
  have hstable : (prefixWord ++ tailWord_2733562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733562).length < 2 ^ (prefixWord ++ tailWord_2733562).sum := by decide
  have hdescent : baseEnd_2733562 < baseStart_2733562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733599 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 6]
def baseStart_2733599 : Nat := 118140960795 + 2733599 * 2 ^ 59
def prefixEnd_2733599 : Nat := 4983230072969 + 3 ^ 40 * 2733599 * 2
def baseEnd_2733599 : Nat := 155961133738883946115657

theorem tailTrace_2733599 : CollatzResearch.WordTrace tailWord_2733599 prefixEnd_2733599 155961133738883946115657 := by
  unfold tailWord_2733599
  simp only [CollatzResearch.WordTrace]
  refine ⟨99702546423645159385563851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66468364282430106257042567 99702546423645159385563851)
  ·
    refine ⟨149553819635467739078345777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99702546423645159385563851 149553819635467739078345777)
    ·
      refine ⟨112165364726600804308759333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149553819635467739078345777 112165364726600804308759333)
      ·
        refine ⟨21031005886237650807892375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112165364726600804308759333 21031005886237650807892375)
        ·
          refine ⟨31546508829356476211838563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21031005886237650807892375 31546508829356476211838563)
          ·
            refine ⟨47319763244034714317757845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31546508829356476211838563 47319763244034714317757845)
            ·
              refine ⟨2218113902064127233644899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47319763244034714317757845 2218113902064127233644899)
              ·
                refine ⟨3327170853096190850467349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2218113902064127233644899 3327170853096190850467349)
                ·
                  refine ⟨155961133738883946115657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3327170853096190850467349 155961133738883946115657)
                  ·
                    rfl

theorem cell23_2733599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 6].length) (baseStart_2733599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733599 prefixEnd_2733599 := by exact prefixLift 2733599
  have htrace : WordTrace (prefixWord ++ tailWord_2733599) baseStart_2733599 baseEnd_2733599 := by
    simpa [prefixWord, tailWord_2733599, baseEnd_2733599] using wordTrace_append hprefix tailTrace_2733599
  have hstable : (prefixWord ++ tailWord_2733599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733599).length < 2 ^ (prefixWord ++ tailWord_2733599).sum := by decide
  have hdescent : baseEnd_2733599 < baseStart_2733599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733602 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2733602 : Nat := 118140960795 + 2733602 * 2 ^ 59
def prefixEnd_2733602 : Nat := 4983230072969 + 3 ^ 40 * 2733602 * 2
def baseEnd_2733602 : Nat := 1403651744091919003303399

theorem tailTrace_2733602 : CollatzResearch.WordTrace tailWord_2733602 prefixEnd_2733602 1403651744091919003303399 := by
  unfold tailWord_2733602
  simp only [CollatzResearch.WordTrace]
  refine ⟨24925663960658572724480765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66468437228422860598615373 24925663960658572724480765)
  ·
    refine ⟨9347123985246964771680287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24925663960658572724480765 9347123985246964771680287)
    ·
      refine ⟨14020685977870447157520431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9347123985246964771680287 14020685977870447157520431)
      ·
        refine ⟨21031028966805670736280647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14020685977870447157520431 21031028966805670736280647)
        ·
          refine ⟨31546543450208506104420971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21031028966805670736280647 31546543450208506104420971)
          ·
            refine ⟨47319815175312759156631457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31546543450208506104420971 47319815175312759156631457)
            ·
              refine ⟨35489861381484569367473593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47319815175312759156631457 35489861381484569367473593)
              ·
                refine ⟨26617396036113427025605195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35489861381484569367473593 26617396036113427025605195)
                ·
                  refine ⟨39926094054170140538407793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26617396036113427025605195 39926094054170140538407793)
                  ·
                    refine ⟨29944570540627605403805845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39926094054170140538407793 29944570540627605403805845)
                    ·
                      refine ⟨1403651744091919003303399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29944570540627605403805845 1403651744091919003303399)
                      ·
                        rfl

theorem cell23_2733602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2733602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733602 prefixEnd_2733602 := by exact prefixLift 2733602
  have htrace : WordTrace (prefixWord ++ tailWord_2733602) baseStart_2733602 baseEnd_2733602 := by
    simpa [prefixWord, tailWord_2733602, baseEnd_2733602] using wordTrace_append hprefix tailTrace_2733602
  have hstable : (prefixWord ++ tailWord_2733602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733602).length < 2 ^ (prefixWord ++ tailWord_2733602).sum := by decide
  have hdescent : baseEnd_2733602 < baseStart_2733602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733642 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_2733642 : Nat := 118140960795 + 2733642 * 2 ^ 59
def prefixEnd_2733642 : Nat := 4983230072969 + 3 ^ 40 * 2733642 * 2
def baseEnd_2733642 : Nat := 467890761106032948934405

theorem tailTrace_2733642 : CollatzResearch.WordTrace tailWord_2733642 prefixEnd_2733642 467890761106032948934405 := by
  unfold tailWord_2733642
  simp only [CollatzResearch.WordTrace]
  refine ⟨24926028690622344432344795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66469409841659585152919453 24926028690622344432344795)
  ·
    refine ⟨37389043035933516648517193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24926028690622344432344795 37389043035933516648517193)
    ·
      refine ⟨28041782276950137486387895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37389043035933516648517193 28041782276950137486387895)
      ·
        refine ⟨42062673415425206229581843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28041782276950137486387895 42062673415425206229581843)
        ·
          refine ⟨63094010123137809344372765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42062673415425206229581843 63094010123137809344372765)
          ·
            refine ⟨23660253796176678504139787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63094010123137809344372765 23660253796176678504139787)
            ·
              refine ⟨35490380694265017756209681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23660253796176678504139787 35490380694265017756209681)
              ·
                refine ⟨26617785520698763317157261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35490380694265017756209681 26617785520698763317157261)
                ·
                  refine ⟨9981669570262036243933973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26617785520698763317157261 9981669570262036243933973)
                  ·
                    refine ⟨467890761106032948934405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9981669570262036243933973 467890761106032948934405)
                    ·
                      rfl

theorem cell23_2733642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_2733642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733642 prefixEnd_2733642 := by exact prefixLift 2733642
  have htrace : WordTrace (prefixWord ++ tailWord_2733642) baseStart_2733642 baseEnd_2733642 := by
    simpa [prefixWord, tailWord_2733642, baseEnd_2733642] using wordTrace_append hprefix tailTrace_2733642
  have hstable : (prefixWord ++ tailWord_2733642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733642).length < 2 ^ (prefixWord ++ tailWord_2733642).sum := by decide
  have hdescent : baseEnd_2733642 < baseStart_2733642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733692 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_2733692 : Nat := 118140960795 + 2733692 * 2 ^ 59
def prefixEnd_2733692 : Nat := 4983230072969 + 3 ^ 40 * 2733692 * 2
def baseEnd_2733692 : Nat := 1403697957350823651177985

theorem tailTrace_2733692 : CollatzResearch.WordTrace tailWord_2733692 prefixEnd_2733692 1403697957350823651177985 := by
  unfold tailWord_2733692
  simp only [CollatzResearch.WordTrace]
  refine ⟨49852969206154118134349665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66470625608205490845799553 49852969206154118134349665)
  ·
    refine ⟨37389726904615588600762249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49852969206154118134349665 37389726904615588600762249)
    ·
      refine ⟨28042295178461691450571687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37389726904615588600762249 28042295178461691450571687)
      ·
        refine ⟨42063442767692537175857531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28042295178461691450571687 42063442767692537175857531)
        ·
          refine ⟨63095164151538805763786297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42063442767692537175857531 63095164151538805763786297)
          ·
            refine ⟨47321373113654104322839723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63095164151538805763786297 47321373113654104322839723)
            ·
              refine ⟨70982059670481156484259585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47321373113654104322839723 70982059670481156484259585)
              ·
                refine ⟨53236544752860867363194689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70982059670481156484259585 53236544752860867363194689)
                ·
                  refine ⟨39927408564645650522396017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53236544752860867363194689 39927408564645650522396017)
                  ·
                    refine ⟨29945556423484237891797013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39927408564645650522396017 29945556423484237891797013)
                    ·
                      refine ⟨1403697957350823651177985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29945556423484237891797013 1403697957350823651177985)
                      ·
                        rfl

theorem cell23_2733692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_2733692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733692 prefixEnd_2733692 := by exact prefixLift 2733692
  have htrace : WordTrace (prefixWord ++ tailWord_2733692) baseStart_2733692 baseEnd_2733692 := by
    simpa [prefixWord, tailWord_2733692, baseEnd_2733692] using wordTrace_append hprefix tailTrace_2733692
  have hstable : (prefixWord ++ tailWord_2733692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733692).length < 2 ^ (prefixWord ++ tailWord_2733692).sum := by decide
  have hdescent : baseEnd_2733692 < baseStart_2733692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733693 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_2733693 : Nat := 118140960795 + 2733693 * 2 ^ 59
def prefixEnd_2733693 : Nat := 4983230072969 + 3 ^ 40 * 2733693 * 2
def baseEnd_2733693 : Nat := 467899490277159382421827

theorem tailTrace_2733693 : CollatzResearch.WordTrace tailWord_2733693 prefixEnd_2733693 467899490277159382421827 := by
  unfold tailWord_2733693
  simp only [CollatzResearch.WordTrace]
  refine ⟨99705974885304613439485733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66470649923536408959657155 99705974885304613439485733)
  ·
    refine ⟨18694870290994615019903575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99705974885304613439485733 18694870290994615019903575)
    ·
      refine ⟨28042305436491922529855363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18694870290994615019903575 28042305436491922529855363)
      ·
        refine ⟨42063458154737883794783045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28042305436491922529855363 42063458154737883794783045)
        ·
          refine ⟨7886898404013353211521821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42063458154737883794783045 7886898404013353211521821)
          ·
            refine ⟨2957586901505007454320683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7886898404013353211521821 2957586901505007454320683)
            ·
              refine ⟨4436380352257511181481025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2957586901505007454320683 4436380352257511181481025)
              ·
                refine ⟨3327285264193133386110769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4436380352257511181481025 3327285264193133386110769)
                ·
                  refine ⟨2495463948144850039583077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3327285264193133386110769 2495463948144850039583077)
                  ·
                    refine ⟨467899490277159382421827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495463948144850039583077 467899490277159382421827)
                    ·
                      rfl

theorem cell23_2733693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_2733693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733693 prefixEnd_2733693 := by exact prefixLift 2733693
  have htrace : WordTrace (prefixWord ++ tailWord_2733693) baseStart_2733693 baseEnd_2733693 := by
    simpa [prefixWord, tailWord_2733693, baseEnd_2733693] using wordTrace_append hprefix tailTrace_2733693
  have hstable : (prefixWord ++ tailWord_2733693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733693).length < 2 ^ (prefixWord ++ tailWord_2733693).sum := by decide
  have hdescent : baseEnd_2733693 < baseStart_2733693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733700 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_2733700 : Nat := 118140960795 + 2733700 * 2 ^ 59
def prefixEnd_2733700 : Nat := 4983230072969 + 3 ^ 40 * 2733700 * 2
def baseEnd_2733700 : Nat := 1403702065196059619877949

theorem tailTrace_2733700 : CollatzResearch.WordTrace tailWord_2733700 prefixEnd_2733700 1403702065196059619877949 := by
  unfold tailWord_2733700
  simp only [CollatzResearch.WordTrace]
  refine ⟨49853115098139626817495277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66470820130852835756660369 49853115098139626817495277)
  ·
    refine ⟨18694918161802360056560729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49853115098139626817495277 18694918161802360056560729)
    ·
      refine ⟨14021188621351770042420547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18694918161802360056560729 14021188621351770042420547)
      ·
        refine ⟨21031782932027655063630821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14021188621351770042420547 21031782932027655063630821)
        ·
          refine ⟨3943459299755185324430779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21031782932027655063630821 3943459299755185324430779)
          ·
            refine ⟨5915188949632777986646169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3943459299755185324430779 5915188949632777986646169)
            ·
              refine ⟨4436391712224583489984627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5915188949632777986646169 4436391712224583489984627)
              ·
                refine ⟨6654587568336875234976941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4436391712224583489984627 6654587568336875234976941)
                ·
                  refine ⟨2495470338126328213116353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6654587568336875234976941 2495470338126328213116353)
                  ·
                    refine ⟨1871602753594746159837265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2495470338126328213116353 1871602753594746159837265)
                    ·
                      refine ⟨1403702065196059619877949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1871602753594746159837265 1403702065196059619877949)
                      ·
                        rfl

theorem cell23_2733700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_2733700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733700 prefixEnd_2733700 := by exact prefixLift 2733700
  have htrace : WordTrace (prefixWord ++ tailWord_2733700) baseStart_2733700 baseEnd_2733700 := by
    simpa [prefixWord, tailWord_2733700, baseEnd_2733700] using wordTrace_append hprefix tailTrace_2733700
  have hstable : (prefixWord ++ tailWord_2733700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733700).length < 2 ^ (prefixWord ++ tailWord_2733700).sum := by decide
  have hdescent : baseEnd_2733700 < baseStart_2733700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733712 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_2733712 : Nat := 118140960795 + 2733712 * 2 ^ 59
def prefixEnd_2733712 : Nat := 4983230072969 + 3 ^ 40 * 2733712 * 2
def baseEnd_2733712 : Nat := 1403708226963913572927893

theorem tailTrace_2733712 : CollatzResearch.WordTrace tailWord_2733712 prefixEnd_2733712 1403708226963913572927893 := by
  unfold tailWord_2733712
  simp only [CollatzResearch.WordTrace]
  refine ⟨49853333936117889842213695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66471111914823853122951593 49853333936117889842213695)
  ·
    refine ⟨74780000904176834763320543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49853333936117889842213695 74780000904176834763320543)
    ·
      refine ⟨112170001356265252144980815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74780000904176834763320543 112170001356265252144980815)
      ·
        refine ⟨168255002034397878217471223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112170001356265252144980815 168255002034397878217471223)
        ·
          refine ⟨252382503051596817326206835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168255002034397878217471223 252382503051596817326206835)
          ·
            refine ⟨378573754577395225989310253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252382503051596817326206835 378573754577395225989310253)
            ·
              refine ⟨141965157966523209745991345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 378573754577395225989310253 141965157966523209745991345)
              ·
                refine ⟨106473868474892407309493509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141965157966523209745991345 106473868474892407309493509)
                ·
                  refine ⟨19963850339042326370530033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106473868474892407309493509 19963850339042326370530033)
                  ·
                    refine ⟨14972887754281744777897525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19963850339042326370530033 14972887754281744777897525)
                    ·
                      refine ⟨1403708226963913572927893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14972887754281744777897525 1403708226963913572927893)
                      ·
                        rfl

theorem cell23_2733712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_2733712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733712 prefixEnd_2733712 := by exact prefixLift 2733712
  have htrace : WordTrace (prefixWord ++ tailWord_2733712) baseStart_2733712 baseEnd_2733712 := by
    simpa [prefixWord, tailWord_2733712, baseEnd_2733712] using wordTrace_append hprefix tailTrace_2733712
  have hstable : (prefixWord ++ tailWord_2733712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733712).length < 2 ^ (prefixWord ++ tailWord_2733712).sum := by decide
  have hdescent : baseEnd_2733712 < baseStart_2733712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733729 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2733729 : Nat := 118140960795 + 2733729 * 2 ^ 59
def prefixEnd_2733729 : Nat := 4983230072969 + 3 ^ 40 * 2733729 * 2
def baseEnd_2733729 : Nat := 1403716956135040006415315

theorem tailTrace_2733729 : CollatzResearch.WordTrace tailWord_2733729 prefixEnd_2733729 1403716956135040006415315 := by
  unfold tailWord_2733729
  simp only [CollatzResearch.WordTrace]
  refine ⟨99707287913174191587796241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66471525275449461058530827 99707287913174191587796241)
  ·
    refine ⟨74780465934880643690847181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99707287913174191587796241 74780465934880643690847181)
    ·
      refine ⟨28042674725580241384067693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74780465934880643690847181 28042674725580241384067693)
      ·
        refine ⟨10516003022092590519025385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28042674725580241384067693 10516003022092590519025385)
        ·
          refine ⟨7887002266569442889269039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10516003022092590519025385 7887002266569442889269039)
          ·
            refine ⟨11830503399854164333903559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7887002266569442889269039 11830503399854164333903559)
            ·
              refine ⟨17745755099781246500855339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11830503399854164333903559 17745755099781246500855339)
              ·
                refine ⟨26618632649671869751283009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17745755099781246500855339 26618632649671869751283009)
                ·
                  refine ⟨19963974487253902313462257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26618632649671869751283009 19963974487253902313462257)
                  ·
                    refine ⟨14972980865440426735096693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19963974487253902313462257 14972980865440426735096693)
                    ·
                      refine ⟨1403716956135040006415315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14972980865440426735096693 1403716956135040006415315)
                      ·
                        rfl

theorem cell23_2733729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2733729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733729 prefixEnd_2733729 := by exact prefixLift 2733729
  have htrace : WordTrace (prefixWord ++ tailWord_2733729) baseStart_2733729 baseEnd_2733729 := by
    simpa [prefixWord, tailWord_2733729, baseEnd_2733729] using wordTrace_append hprefix tailTrace_2733729
  have hstable : (prefixWord ++ tailWord_2733729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733729).length < 2 ^ (prefixWord ++ tailWord_2733729).sum := by decide
  have hdescent : baseEnd_2733729 < baseStart_2733729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733750 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2733750 : Nat := 118140960795 + 2733750 * 2 ^ 59
def prefixEnd_2733750 : Nat := 4983230072969 + 3 ^ 40 * 2733750 * 2
def baseEnd_2733750 : Nat := 1403727739228784424252719

theorem tailTrace_2733750 : CollatzResearch.WordTrace tailWord_2733750 prefixEnd_2733750 1403727739228784424252719 := by
  unfold tailWord_2733750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231753365381132010894419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66472035897398741449540469 6231753365381132010894419)
  ·
    refine ⟨9347630048071698016341629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6231753365381132010894419 9347630048071698016341629)
    ·
      refine ⟨3505361268026886756128111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9347630048071698016341629 3505361268026886756128111)
      ·
        refine ⟨5258041902040330134192167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505361268026886756128111 5258041902040330134192167)
        ·
          refine ⟨7887062853060495201288251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5258041902040330134192167 7887062853060495201288251)
          ·
            refine ⟨11830594279590742801932377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7887062853060495201288251 11830594279590742801932377)
            ·
              refine ⟨8872945709693057101449283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11830594279590742801932377 8872945709693057101449283)
              ·
                refine ⟨13309418564539585652173925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8872945709693057101449283 13309418564539585652173925)
                ·
                  refine ⟨2495515980851172309782611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13309418564539585652173925 2495515980851172309782611)
                  ·
                    refine ⟨3743273971276758464673917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2495515980851172309782611 3743273971276758464673917)
                    ·
                      refine ⟨1403727739228784424252719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3743273971276758464673917 1403727739228784424252719)
                      ·
                        rfl

theorem cell23_2733750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2733750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733750 prefixEnd_2733750 := by exact prefixLift 2733750
  have htrace : WordTrace (prefixWord ++ tailWord_2733750) baseStart_2733750 baseEnd_2733750 := by
    simpa [prefixWord, tailWord_2733750, baseEnd_2733750] using wordTrace_append hprefix tailTrace_2733750
  have hstable : (prefixWord ++ tailWord_2733750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733750).length < 2 ^ (prefixWord ++ tailWord_2733750).sum := by decide
  have hdescent : baseEnd_2733750 < baseStart_2733750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733759 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 3]
def baseStart_2733759 : Nat := 118140960795 + 2733759 * 2 ^ 59
def prefixEnd_2733759 : Nat := 4983230072969 + 3 ^ 40 * 2733759 * 2
def baseEnd_2733759 : Nat := 1403732360554674889040177

theorem tailTrace_2733759 : CollatzResearch.WordTrace tailWord_2733759 prefixEnd_2733759 1403732360554674889040177 := by
  unfold tailWord_2733759
  simp only [CollatzResearch.WordTrace]
  refine ⟨99708382103065506711388331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66472254735377004474258887 99708382103065506711388331)
  ·
    refine ⟨149562573154598260067082497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99708382103065506711388331 149562573154598260067082497)
    ·
      refine ⟨112171929865948695050311873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149562573154598260067082497 112171929865948695050311873)
      ·
        refine ⟨84128947399461521287733905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112171929865948695050311873 84128947399461521287733905)
        ·
          refine ⟨63096710549596140965800429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84128947399461521287733905 63096710549596140965800429)
          ·
            refine ⟨23661266456098552862175161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63096710549596140965800429 23661266456098552862175161)
            ·
              refine ⟨17745949842073914646631371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23661266456098552862175161 17745949842073914646631371)
              ·
                refine ⟨26618924763110871969947057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17745949842073914646631371 26618924763110871969947057)
                ·
                  refine ⟨19964193572333153977460293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26618924763110871969947057 19964193572333153977460293)
                  ·
                    refine ⟨3743286294812466370773805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19964193572333153977460293 3743286294812466370773805)
                    ·
                      refine ⟨1403732360554674889040177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3743286294812466370773805 1403732360554674889040177)
                      ·
                        rfl

theorem cell23_2733759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_2733759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733759 prefixEnd_2733759 := by exact prefixLift 2733759
  have htrace : WordTrace (prefixWord ++ tailWord_2733759) baseStart_2733759 baseEnd_2733759 := by
    simpa [prefixWord, tailWord_2733759, baseEnd_2733759] using wordTrace_append hprefix tailTrace_2733759
  have hstable : (prefixWord ++ tailWord_2733759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733759).length < 2 ^ (prefixWord ++ tailWord_2733759).sum := by decide
  have hdescent : baseEnd_2733759 < baseStart_2733759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733796 : List Nat := [2, 3, 1, 1, 1, 3, 2, 5, 5]
def baseStart_2733796 : Nat := 118140960795 + 2733796 * 2 ^ 59
def prefixEnd_2733796 : Nat := 4983230072969 + 3 ^ 40 * 2733796 * 2
def baseEnd_2733796 : Nat := 155972373259876804919723

theorem tailTrace_2733796 : CollatzResearch.WordTrace tailWord_2733796 prefixEnd_2733796 155972373259876804919723 := by
  unfold tailWord_2733796
  simp only [CollatzResearch.WordTrace]
  refine ⟨49854865801965731015242621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66473154402620974686990161 49854865801965731015242621)
  ·
    refine ⟨18695574675737149130715983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49854865801965731015242621 18695574675737149130715983)
    ·
      refine ⟨28043362013605723696073975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18695574675737149130715983 28043362013605723696073975)
      ·
        refine ⟨42065043020408585544110963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28043362013605723696073975 42065043020408585544110963)
        ·
          refine ⟨63097564530612878316166445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42065043020408585544110963 63097564530612878316166445)
          ·
            refine ⟨23661586698979829368562417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63097564530612878316166445 23661586698979829368562417)
            ·
              refine ⟨17746190024234872026421813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23661586698979829368562417 17746190024234872026421813)
              ·
                refine ⟨1663705314772019252477045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17746190024234872026421813 1663705314772019252477045)
                ·
                  refine ⟨155972373259876804919723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1663705314772019252477045 155972373259876804919723)
                  ·
                    rfl

theorem cell23_2733796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_2733796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733796 prefixEnd_2733796 := by exact prefixLift 2733796
  have htrace : WordTrace (prefixWord ++ tailWord_2733796) baseStart_2733796 baseEnd_2733796 := by
    simpa [prefixWord, tailWord_2733796, baseEnd_2733796] using wordTrace_append hprefix tailTrace_2733796
  have hstable : (prefixWord ++ tailWord_2733796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733796).length < 2 ^ (prefixWord ++ tailWord_2733796).sum := by decide
  have hdescent : baseEnd_2733796 < baseStart_2733796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733806 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_2733806 : Nat := 118140960795 + 2733806 * 2 ^ 59
def prefixEnd_2733806 : Nat := 4983230072969 + 3 ^ 40 * 2733806 * 2
def baseEnd_2733806 : Nat := 1403756494145436205152461

theorem tailTrace_2733806 : CollatzResearch.WordTrace tailWord_2733806 prefixEnd_2733806 1403756494145436205152461 := by
  unfold tailWord_2733806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12463762041736904217293659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66473397555930155825566181 12463762041736904217293659)
  ·
    refine ⟨18695643062605356325940489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12463762041736904217293659 18695643062605356325940489)
    ·
      refine ⟨14021732296954017244455367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18695643062605356325940489 14021732296954017244455367)
      ·
        refine ⟨21032598445431025866683051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14021732296954017244455367 21032598445431025866683051)
        ·
          refine ⟨31548897668146538800024577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21032598445431025866683051 31548897668146538800024577)
          ·
            refine ⟨23661673251109904100018433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31548897668146538800024577 23661673251109904100018433)
            ·
              refine ⟨17746254938332428075013825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23661673251109904100018433 17746254938332428075013825)
              ·
                refine ⟨13309691203749321056260369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17746254938332428075013825 13309691203749321056260369)
                ·
                  refine ⟨9982268402811990792195277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13309691203749321056260369 9982268402811990792195277)
                  ·
                    refine ⟨3743350651054496547073229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9982268402811990792195277 3743350651054496547073229)
                    ·
                      refine ⟨1403756494145436205152461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3743350651054496547073229 1403756494145436205152461)
                      ·
                        rfl

theorem cell23_2733806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_2733806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733806 prefixEnd_2733806 := by exact prefixLift 2733806
  have htrace : WordTrace (prefixWord ++ tailWord_2733806) baseStart_2733806 baseEnd_2733806 := by
    simpa [prefixWord, tailWord_2733806, baseEnd_2733806] using wordTrace_append hprefix tailTrace_2733806
  have hstable : (prefixWord ++ tailWord_2733806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733806).length < 2 ^ (prefixWord ++ tailWord_2733806).sum := by decide
  have hdescent : baseEnd_2733806 < baseStart_2733806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733826 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2733826 : Nat := 118140960795 + 2733826 * 2 ^ 59
def prefixEnd_2733826 : Nat := 4983230072969 + 3 ^ 40 * 2733826 * 2
def baseEnd_2733826 : Nat := 467922254586175375634123

theorem tailTrace_2733826 : CollatzResearch.WordTrace tailWord_2733826 prefixEnd_2733826 467922254586175375634123 := by
  unfold tailWord_2733826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24927706448455694288519333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66473883862548518102718221 24927706448455694288519333)
  ·
    refine ⟨4673944959085442679097375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24927706448455694288519333 4673944959085442679097375)
    ·
      refine ⟨7010917438628164018646063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4673944959085442679097375 7010917438628164018646063)
      ·
        refine ⟨10516376157942246027969095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010917438628164018646063 10516376157942246027969095)
        ·
          refine ⟨15774564236913369041953643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10516376157942246027969095 15774564236913369041953643)
          ·
            refine ⟨23661846355370053562930465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15774564236913369041953643 23661846355370053562930465)
            ·
              refine ⟨17746384766527540172197849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23661846355370053562930465 17746384766527540172197849)
              ·
                refine ⟨13309788574895655129148387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17746384766527540172197849 13309788574895655129148387)
                ·
                  refine ⟨19964682862343482693722581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13309788574895655129148387 19964682862343482693722581)
                  ·
                    refine ⟨467922254586175375634123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19964682862343482693722581 467922254586175375634123)
                    ·
                      rfl

theorem cell23_2733826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2733826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733826 prefixEnd_2733826 := by exact prefixLift 2733826
  have htrace : WordTrace (prefixWord ++ tailWord_2733826) baseStart_2733826 baseEnd_2733826 := by
    simpa [prefixWord, tailWord_2733826, baseEnd_2733826] using wordTrace_append hprefix tailTrace_2733826
  have hstable : (prefixWord ++ tailWord_2733826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733826).length < 2 ^ (prefixWord ++ tailWord_2733826).sum := by decide
  have hdescent : baseEnd_2733826 < baseStart_2733826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733856 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 5, 4]
def baseStart_2733856 : Nat := 118140960795 + 2733856 * 2 ^ 59
def prefixEnd_2733856 : Nat := 4983230072969 + 3 ^ 40 * 2733856 * 2
def baseEnd_2733856 : Nat := 467927389392720336509077

theorem tailTrace_2733856 : CollatzResearch.WordTrace tailWord_2733856 prefixEnd_2733856 467927389392720336509077 := by
  unfold tailWord_2733856
  simp only [CollatzResearch.WordTrace]
  refine ⟨49855959991857046138834711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66474613322476061518446281 49855959991857046138834711)
  ·
    refine ⟨74783939987785569208252067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49855959991857046138834711 74783939987785569208252067)
    ·
      refine ⟨112175909981678353812378101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74783939987785569208252067 112175909981678353812378101)
      ·
        refine ⟨10516491560782345669910447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112175909981678353812378101 10516491560782345669910447)
        ·
          refine ⟨15774737341173518504865671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10516491560782345669910447 15774737341173518504865671)
          ·
            refine ⟨23662106011760277757298507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15774737341173518504865671 23662106011760277757298507)
            ·
              refine ⟨35493159017640416635947761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23662106011760277757298507 35493159017640416635947761)
              ·
                refine ⟨26619869263230312476960821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35493159017640416635947761 26619869263230312476960821)
                ·
                  refine ⟨2495612743427841794715077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26619869263230312476960821 2495612743427841794715077)
                  ·
                    refine ⟨467927389392720336509077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495612743427841794715077 467927389392720336509077)
                    ·
                      rfl

theorem cell23_2733856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 4].length) (baseStart_2733856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733856 prefixEnd_2733856 := by exact prefixLift 2733856
  have htrace : WordTrace (prefixWord ++ tailWord_2733856) baseStart_2733856 baseEnd_2733856 := by
    simpa [prefixWord, tailWord_2733856, baseEnd_2733856] using wordTrace_append hprefix tailTrace_2733856
  have hstable : (prefixWord ++ tailWord_2733856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733856).length < 2 ^ (prefixWord ++ tailWord_2733856).sum := by decide
  have hdescent : baseEnd_2733856 < baseStart_2733856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733859 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 6]
def baseStart_2733859 : Nat := 118140960795 + 2733859 * 2 ^ 59
def prefixEnd_2733859 : Nat := 4983230072969 + 3 ^ 40 * 2733859 * 2
def baseEnd_2733859 : Nat := 1403783708620124497789717

theorem tailTrace_2733859 : CollatzResearch.WordTrace tailWord_2733859 prefixEnd_2733859 1403783708620124497789717 := by
  unfold tailWord_2733859
  simp only [CollatzResearch.WordTrace]
  refine ⟨99712029402703223790028631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66474686268468815860019087 99712029402703223790028631)
  ·
    refine ⟨149568044104054835685042947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99712029402703223790028631 149568044104054835685042947)
    ·
      refine ⟨224352066156082253527564421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149568044104054835685042947 224352066156082253527564421)
      ·
        refine ⟨42066012404265422536418329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224352066156082253527564421 42066012404265422536418329)
        ·
          refine ⟨31549509303199066902313747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42066012404265422536418329 31549509303199066902313747)
          ·
            refine ⟨47324263954798600353470621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31549509303199066902313747 47324263954798600353470621)
            ·
              refine ⟨17746598983049475132551483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47324263954798600353470621 17746598983049475132551483)
              ·
                refine ⟨26619898474574212698827225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17746598983049475132551483 26619898474574212698827225)
                ·
                  refine ⟨19964923855930659524120419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26619898474574212698827225 19964923855930659524120419)
                  ·
                    refine ⟨29947385783895989286180629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19964923855930659524120419 29947385783895989286180629)
                    ·
                      refine ⟨1403783708620124497789717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29947385783895989286180629 1403783708620124497789717)
                      ·
                        rfl

theorem cell23_2733859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_2733859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733859 prefixEnd_2733859 := by exact prefixLift 2733859
  have htrace : WordTrace (prefixWord ++ tailWord_2733859) baseStart_2733859 baseEnd_2733859 := by
    simpa [prefixWord, tailWord_2733859, baseEnd_2733859] using wordTrace_append hprefix tailTrace_2733859
  have hstable : (prefixWord ++ tailWord_2733859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733859).length < 2 ^ (prefixWord ++ tailWord_2733859).sum := by decide
  have hdescent : baseEnd_2733859 < baseStart_2733859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733873 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 3, 4]
def baseStart_2733873 : Nat := 118140960795 + 2733873 * 2 ^ 59
def prefixEnd_2733873 : Nat := 4983230072969 + 3 ^ 40 * 2733873 * 2
def baseEnd_2733873 : Nat := 467930299116429147671551

theorem tailTrace_2733873 : CollatzResearch.WordTrace tailWord_2733873 prefixEnd_2733873 467930299116429147671551 := by
  unfold tailWord_2733873
  simp only [CollatzResearch.WordTrace]
  refine ⟨99712540024652504181038273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66475026683101669454025515 99712540024652504181038273)
  ·
    refine ⟨74784405018489378135778705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99712540024652504181038273 74784405018489378135778705)
    ·
      refine ⟨56088303763867033601834029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74784405018489378135778705 56088303763867033601834029)
      ·
        refine ⟨21033113911450137600687761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56088303763867033601834029 21033113911450137600687761)
        ·
          refine ⟨15774835433587603200515821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21033113911450137600687761 15774835433587603200515821)
          ·
            refine ⟨5915563287595351200193433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15774835433587603200515821 5915563287595351200193433)
            ·
              refine ⟨4436672465696513400145075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5915563287595351200193433 4436672465696513400145075)
              ·
                refine ⟨6655008698544770100217613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4436672465696513400145075 6655008698544770100217613)
                ·
                  refine ⟨2495628261954288787581605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6655008698544770100217613 2495628261954288787581605)
                  ·
                    refine ⟨467930299116429147671551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495628261954288787581605 467930299116429147671551)
                    ·
                      rfl

theorem cell23_2733873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_2733873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733873 prefixEnd_2733873 := by exact prefixLift 2733873
  have htrace : WordTrace (prefixWord ++ tailWord_2733873) baseStart_2733873 baseEnd_2733873 := by
    simpa [prefixWord, tailWord_2733873, baseEnd_2733873] using wordTrace_append hprefix tailTrace_2733873
  have hstable : (prefixWord ++ tailWord_2733873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733873).length < 2 ^ (prefixWord ++ tailWord_2733873).sum := by decide
  have hdescent : baseEnd_2733873 < baseStart_2733873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733936 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_2733936 : Nat := 118140960795 + 2733936 * 2 ^ 59
def prefixEnd_2733936 : Nat := 4983230072969 + 3 ^ 40 * 2733936 * 2
def baseEnd_2733936 : Nat := 1403823246630520696526863

theorem tailTrace_2733936 : CollatzResearch.WordTrace tailWord_2733936 prefixEnd_2733936 1403823246630520696526863 := by
  unfold tailWord_2733936
  simp only [CollatzResearch.WordTrace]
  refine ⟨49857418911712132970290831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66476558548949510627054441 49857418911712132970290831)
  ·
    refine ⟨74786128367568199455436247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49857418911712132970290831 74786128367568199455436247)
    ·
      refine ⟨112179192551352299183154371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74786128367568199455436247 112179192551352299183154371)
      ·
        refine ⟨168268788827028448774731557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112179192551352299183154371 168268788827028448774731557)
        ·
          refine ⟨31550397905067834145262167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168268788827028448774731557 31550397905067834145262167)
          ·
            refine ⟨47325596857601751217893251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31550397905067834145262167 47325596857601751217893251)
            ·
              refine ⟨70988395286402626826839877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47325596857601751217893251 70988395286402626826839877)
              ·
                refine ⟨13310324116200492530032477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70988395286402626826839877 13310324116200492530032477)
                ·
                  refine ⟨4991371543575184698762179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13310324116200492530032477 4991371543575184698762179)
                  ·
                    refine ⟨7487057315362777048143269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4991371543575184698762179 7487057315362777048143269)
                    ·
                      refine ⟨1403823246630520696526863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7487057315362777048143269 1403823246630520696526863)
                      ·
                        rfl

theorem cell23_2733936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_2733936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733936 prefixEnd_2733936 := by exact prefixLift 2733936
  have htrace : WordTrace (prefixWord ++ tailWord_2733936) baseStart_2733936 baseEnd_2733936 := by
    simpa [prefixWord, tailWord_2733936, baseEnd_2733936] using wordTrace_append hprefix tailTrace_2733936
  have hstable : (prefixWord ++ tailWord_2733936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733936).length < 2 ^ (prefixWord ++ tailWord_2733936).sum := by decide
  have hdescent : baseEnd_2733936 < baseStart_2733936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733950 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2733950 : Nat := 118140960795 + 2733950 * 2 ^ 59
def prefixEnd_2733950 : Nat := 4983230072969 + 3 ^ 40 * 2733950 * 2
def baseEnd_2733950 : Nat := 467943478453227880583933

theorem tailTrace_2733950 : CollatzResearch.WordTrace tailWord_2733950 prefixEnd_2733950 467943478453227880583933 := by
  unfold tailWord_2733950
  simp only [CollatzResearch.WordTrace]
  refine ⟨12464418555671693291448913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66476898963582364221060869 12464418555671693291448913)
  ·
    refine ⟨9348313916753769968586685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12464418555671693291448913 9348313916753769968586685)
    ·
      refine ⟨3505617718782663738220007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9348313916753769968586685 3505617718782663738220007)
      ·
        refine ⟨5258426578173995607330011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505617718782663738220007 5258426578173995607330011)
        ·
          refine ⟨7887639867260993410995017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5258426578173995607330011 7887639867260993410995017)
          ·
            refine ⟨5915729900445745058246263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7887639867260993410995017 5915729900445745058246263)
            ·
              refine ⟨8873594850668617587369395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5915729900445745058246263 8873594850668617587369395)
              ·
                refine ⟨13310392276002926381054093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8873594850668617587369395 13310392276002926381054093)
                ·
                  refine ⟨4991397103501097392895285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13310392276002926381054093 4991397103501097392895285)
                  ·
                    refine ⟨467943478453227880583933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4991397103501097392895285 467943478453227880583933)
                    ·
                      rfl

theorem cell23_2733950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2733950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733950 prefixEnd_2733950 := by exact prefixLift 2733950
  have htrace : WordTrace (prefixWord ++ tailWord_2733950) baseStart_2733950 baseEnd_2733950 := by
    simpa [prefixWord, tailWord_2733950, baseEnd_2733950] using wordTrace_append hprefix tailTrace_2733950
  have hstable : (prefixWord ++ tailWord_2733950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733950).length < 2 ^ (prefixWord ++ tailWord_2733950).sum := by decide
  have hdescent : baseEnd_2733950 < baseStart_2733950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733956 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2733956 : Nat := 118140960795 + 2733956 * 2 ^ 59
def prefixEnd_2733956 : Nat := 4983230072969 + 3 ^ 40 * 2733956 * 2
def baseEnd_2733956 : Nat := 1403833516243610618276771

theorem tailTrace_2733956 : CollatzResearch.WordTrace tailWord_2733956 prefixEnd_2733956 1403833516243610618276771 := by
  unfold tailWord_2733956
  simp only [CollatzResearch.WordTrace]
  refine ⟨49857783641675904678154861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66477044855567872904206481 49857783641675904678154861)
  ·
    refine ⟨18696668865628464254308073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49857783641675904678154861 18696668865628464254308073)
    ·
      refine ⟨14022501649221348190731055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18696668865628464254308073 14022501649221348190731055)
      ·
        refine ⟨21033752473832022286096583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14022501649221348190731055 21033752473832022286096583)
        ·
          refine ⟨31550628710748033429144875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21033752473832022286096583 31550628710748033429144875)
          ·
            refine ⟨47325943066122050143717313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31550628710748033429144875 47325943066122050143717313)
            ·
              refine ⟨35494457299591537607787985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47325943066122050143717313 35494457299591537607787985)
              ·
                refine ⟨26620842974693653205840989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35494457299591537607787985 26620842974693653205840989)
                ·
                  refine ⟨9982816115510119952190371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26620842974693653205840989 9982816115510119952190371)
                  ·
                    refine ⟨14974224173265179928285557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9982816115510119952190371 14974224173265179928285557)
                    ·
                      refine ⟨1403833516243610618276771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14974224173265179928285557 1403833516243610618276771)
                      ·
                        rfl

theorem cell23_2733956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2733956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733956 prefixEnd_2733956 := by exact prefixLift 2733956
  have htrace : WordTrace (prefixWord ++ tailWord_2733956) baseStart_2733956 baseEnd_2733956 := by
    simpa [prefixWord, tailWord_2733956, baseEnd_2733956] using wordTrace_append hprefix tailTrace_2733956
  have hstable : (prefixWord ++ tailWord_2733956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733956).length < 2 ^ (prefixWord ++ tailWord_2733956).sum := by decide
  have hdescent : baseEnd_2733956 < baseStart_2733956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733976 : List Nat := [2, 1, 2, 6, 12]
def baseStart_2733976 : Nat := 118140960795 + 2733976 * 2 ^ 59
def prefixEnd_2733976 : Nat := 4983230072969 + 3 ^ 40 * 2733976 * 2
def baseEnd_2733976 : Nat := 1925711640406996625551

theorem tailTrace_2733976 : CollatzResearch.WordTrace tailWord_2733976 prefixEnd_2733976 1925711640406996625551 := by
  unfold tailWord_2733976
  simp only [CollatzResearch.WordTrace]
  refine ⟨49858148371639676386018891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66477531162186235181358521 49858148371639676386018891)
  ·
    refine ⟨74787222557459514579028337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49858148371639676386018891 74787222557459514579028337)
    ·
      refine ⟨56090416918094635934271253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74787222557459514579028337 56090416918094635934271253)
      ·
        refine ⟨2629238293035686059418965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56090416918094635934271253 2629238293035686059418965)
        ·
          refine ⟨1925711640406996625551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2629238293035686059418965 1925711640406996625551)
          ·
            rfl

theorem cell23_2733976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 12].length) (baseStart_2733976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733976 prefixEnd_2733976 := by exact prefixLift 2733976
  have htrace : WordTrace (prefixWord ++ tailWord_2733976) baseStart_2733976 baseEnd_2733976 := by
    simpa [prefixWord, tailWord_2733976, baseEnd_2733976] using wordTrace_append hprefix tailTrace_2733976
  have hstable : (prefixWord ++ tailWord_2733976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733976).length < 2 ^ (prefixWord ++ tailWord_2733976).sum := by decide
  have hdescent : baseEnd_2733976 < baseStart_2733976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2733980 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_2733980 : Nat := 118140960795 + 2733980 * 2 ^ 59
def prefixEnd_2733980 : Nat := 4983230072969 + 3 ^ 40 * 2733980 * 2
def baseEnd_2733980 : Nat := 467948613259772841458887

theorem tailTrace_2733980 : CollatzResearch.WordTrace tailWord_2733980 prefixEnd_2733980 467948613259772841458887 := by
  unfold tailWord_2733980
  simp only [CollatzResearch.WordTrace]
  refine ⟨49858221317632430727591697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66477628423509907636788929 49858221317632430727591697)
  ·
    refine ⟨37393665988224323045693773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49858221317632430727591697 37393665988224323045693773)
    ·
      refine ⟨14022624745584121142135165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37393665988224323045693773 14022624745584121142135165)
      ·
        refine ⟨5258484279594045428300687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14022624745584121142135165 5258484279594045428300687)
        ·
          refine ⟨7887726419391068142451031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5258484279594045428300687 7887726419391068142451031)
          ·
            refine ⟨11831589629086602213676547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7887726419391068142451031 11831589629086602213676547)
            ·
              refine ⟨17747384443629903320514821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11831589629086602213676547 17747384443629903320514821)
              ·
                refine ⟨3327634583180606872596529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17747384443629903320514821 3327634583180606872596529)
                ·
                  refine ⟨2495725937385455154447397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3327634583180606872596529 2495725937385455154447397)
                  ·
                    refine ⟨467948613259772841458887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495725937385455154447397 467948613259772841458887)
                    ·
                      rfl

theorem cell23_2733980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_2733980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2733980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2733980 prefixEnd_2733980 := by exact prefixLift 2733980
  have htrace : WordTrace (prefixWord ++ tailWord_2733980) baseStart_2733980 baseEnd_2733980 := by
    simpa [prefixWord, tailWord_2733980, baseEnd_2733980] using wordTrace_append hprefix tailTrace_2733980
  have hstable : (prefixWord ++ tailWord_2733980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2733980).length < 2 ^ (prefixWord ++ tailWord_2733980).sum := by decide
  have hdescent : baseEnd_2733980 < baseStart_2733980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2733980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734003 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 3]
def baseStart_2734003 : Nat := 118140960795 + 2734003 * 2 ^ 59
def prefixEnd_2734003 : Nat := 4983230072969 + 3 ^ 40 * 2734003 * 2
def baseEnd_2734003 : Nat := 1403857649834371934389055

theorem tailTrace_2734003 : CollatzResearch.WordTrace tailWord_2734003 prefixEnd_2734003 1403857649834371934389055 := by
  unfold tailWord_2734003
  simp only [CollatzResearch.WordTrace]
  refine ⟨99717281514181536383270663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66478187676121024255513775 99717281514181536383270663)
  ·
    refine ⟨149575922271272304574905995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99717281514181536383270663 149575922271272304574905995)
    ·
      refine ⟨224363883406908456862358993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149575922271272304574905995 224363883406908456862358993)
      ·
        refine ⟨168272912555181342646769245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224363883406908456862358993 168272912555181342646769245)
        ·
          refine ⟨63102342208193003492538467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168272912555181342646769245 63102342208193003492538467)
          ·
            refine ⟨94653513312289505238807701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63102342208193003492538467 94653513312289505238807701)
            ·
              refine ⟨4436883436513570558069111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94653513312289505238807701 4436883436513570558069111)
              ·
                refine ⟨6655325154770355837103667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4436883436513570558069111 6655325154770355837103667)
                ·
                  refine ⟨9982987732155533755655501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6655325154770355837103667 9982987732155533755655501)
                  ·
                    refine ⟨3743620399558325158370813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9982987732155533755655501 3743620399558325158370813)
                    ·
                      refine ⟨1403857649834371934389055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3743620399558325158370813 1403857649834371934389055)
                      ·
                        rfl

theorem cell23_2734003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_2734003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734003 prefixEnd_2734003 := by exact prefixLift 2734003
  have htrace : WordTrace (prefixWord ++ tailWord_2734003) baseStart_2734003 baseEnd_2734003 := by
    simpa [prefixWord, tailWord_2734003, baseEnd_2734003] using wordTrace_append hprefix tailTrace_2734003
  have hstable : (prefixWord ++ tailWord_2734003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734003).length < 2 ^ (prefixWord ++ tailWord_2734003).sum := by decide
  have hdescent : baseEnd_2734003 < baseStart_2734003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734016 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_2734016 : Nat := 118140960795 + 2734016 * 2 ^ 59
def prefixEnd_2734016 : Nat := 4983230072969 + 3 ^ 40 * 2734016 * 2
def baseEnd_2734016 : Nat := 1403864325082880383526495

theorem tailTrace_2734016 : CollatzResearch.WordTrace tailWord_2734016 prefixEnd_2734016 1403864325082880383526495 := by
  unfold tailWord_2734016
  simp only [CollatzResearch.WordTrace]
  refine ⟨49858877831567219801746951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66478503775422959735662601 49858877831567219801746951)
  ·
    refine ⟨74788316747350829702620427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49858877831567219801746951 74788316747350829702620427)
    ·
      refine ⟨112182475121026244553930641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74788316747350829702620427 112182475121026244553930641)
      ·
        refine ⟨84136856340769683415447981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112182475121026244553930641 84136856340769683415447981)
        ·
          refine ⟨31551321127788631280792993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84136856340769683415447981 31551321127788631280792993)
          ·
            refine ⟨23663490845841473460594745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31551321127788631280792993 23663490845841473460594745)
            ·
              refine ⟨17747618134381105095446059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23663490845841473460594745 17747618134381105095446059)
              ·
                refine ⟨26621427201571657643169089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17747618134381105095446059 26621427201571657643169089)
                ·
                  refine ⟨19966070401178743232376817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26621427201571657643169089 19966070401178743232376817)
                  ·
                    refine ⟨14974552800884057424282613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19966070401178743232376817 14974552800884057424282613)
                    ·
                      refine ⟨1403864325082880383526495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14974552800884057424282613 1403864325082880383526495)
                      ·
                        rfl

theorem cell23_2734016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_2734016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734016 prefixEnd_2734016 := by exact prefixLift 2734016
  have htrace : WordTrace (prefixWord ++ tailWord_2734016) baseStart_2734016 baseEnd_2734016 := by
    simpa [prefixWord, tailWord_2734016, baseEnd_2734016] using wordTrace_append hprefix tailTrace_2734016
  have hstable : (prefixWord ++ tailWord_2734016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734016).length < 2 ^ (prefixWord ++ tailWord_2734016).sum := by decide
  have hdescent : baseEnd_2734016 < baseStart_2734016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734037 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2734037 : Nat := 118140960795 + 2734037 * 2 ^ 59
def prefixEnd_2734037 : Nat := 4983230072969 + 3 ^ 40 * 2734037 * 2
def baseEnd_2734037 : Nat := 1403875108176624801363899

theorem tailTrace_2734037 : CollatzResearch.WordTrace tailWord_2734037 prefixEnd_2734037 1403875108176624801363899 := by
  unfold tailWord_2734037
  simp only [CollatzResearch.WordTrace]
  refine ⟨99718521596058360190008365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66479014397372240126672243 99718521596058360190008365)
  ·
    refine ⟨37394445598521885071253137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99718521596058360190008365 37394445598521885071253137)
    ·
      refine ⟨28045834198891413803439853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37394445598521885071253137 28045834198891413803439853)
      ·
        refine ⟨10517187824584280176289945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28045834198891413803439853 10517187824584280176289945)
        ·
          refine ⟨7887890868438210132217459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10517187824584280176289945 7887890868438210132217459)
          ·
            refine ⟨11831836302657315198326189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7887890868438210132217459 11831836302657315198326189)
            ·
              refine ⟨4436938613496493199372321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11831836302657315198326189 4436938613496493199372321)
              ·
                refine ⟨3327703960122369899529241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4436938613496493199372321 3327703960122369899529241)
                ·
                  refine ⟨2495777970091777424646931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3327703960122369899529241 2495777970091777424646931)
                  ·
                    refine ⟨3743666955137666136970397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2495777970091777424646931 3743666955137666136970397)
                    ·
                      refine ⟨1403875108176624801363899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3743666955137666136970397 1403875108176624801363899)
                      ·
                        rfl

theorem cell23_2734037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2734037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734037 prefixEnd_2734037 := by exact prefixLift 2734037
  have htrace : WordTrace (prefixWord ++ tailWord_2734037) baseStart_2734037 baseEnd_2734037 := by
    simpa [prefixWord, tailWord_2734037, baseEnd_2734037] using wordTrace_append hprefix tailTrace_2734037
  have hstable : (prefixWord ++ tailWord_2734037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734037).length < 2 ^ (prefixWord ++ tailWord_2734037).sum := by decide
  have hdescent : baseEnd_2734037 < baseStart_2734037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734130 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_2734130 : Nat := 118140960795 + 2734130 * 2 ^ 59
def prefixEnd_2734130 : Nat := 4983230072969 + 3 ^ 40 * 2734130 * 2
def baseEnd_2734130 : Nat := 467974287292497645833657

theorem tailTrace_2734130 : CollatzResearch.WordTrace tailWord_2734130 prefixEnd_2734130 467974287292497645833657 := by
  unfold tailWord_2734130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24930478396180359268285961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66481275723147624715429229 24930478396180359268285961)
  ·
    refine ⟨18697858797135269451214471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24930478396180359268285961 18697858797135269451214471)
    ·
      refine ⟨28046788195702904176821707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18697858797135269451214471 28046788195702904176821707)
      ·
        refine ⟨42070182293554356265232561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28046788195702904176821707 42070182293554356265232561)
        ·
          refine ⟨31552636720165767198924421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42070182293554356265232561 31552636720165767198924421)
          ·
            refine ⟨5916119385031081349798329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31552636720165767198924421 5916119385031081349798329)
            ·
              refine ⟨4437089538773311012348747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5916119385031081349798329 4437089538773311012348747)
              ·
                refine ⟨6655634308159966518523121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437089538773311012348747 6655634308159966518523121)
                ·
                  refine ⟨4991725731119974888892341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6655634308159966518523121 4991725731119974888892341)
                  ·
                    refine ⟨467974287292497645833657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4991725731119974888892341 467974287292497645833657)
                    ·
                      rfl

theorem cell23_2734130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_2734130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734130 prefixEnd_2734130 := by exact prefixLift 2734130
  have htrace : WordTrace (prefixWord ++ tailWord_2734130) baseStart_2734130 baseEnd_2734130 := by
    simpa [prefixWord, tailWord_2734130, baseEnd_2734130] using wordTrace_append hprefix tailTrace_2734130
  have hstable : (prefixWord ++ tailWord_2734130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734130).length < 2 ^ (prefixWord ++ tailWord_2734130).sum := by decide
  have hdescent : baseEnd_2734130 < baseStart_2734130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734133 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2734133 : Nat := 118140960795 + 2734133 * 2 ^ 59
def prefixEnd_2734133 : Nat := 4983230072969 + 3 ^ 40 * 2734133 * 2
def baseEnd_2734133 : Nat := 1403924402319456425763457

theorem tailTrace_2734133 : CollatzResearch.WordTrace tailWord_2734133 prefixEnd_2734133 1403924402319456425763457 := by
  unfold tailWord_2734133
  simp only [CollatzResearch.WordTrace]
  refine ⟨99722023003710568585503053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66481348669140379057002035 99722023003710568585503053)
  ·
    refine ⟨37395758626391463219563645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99722023003710568585503053 37395758626391463219563645)
    ·
      refine ⟨14023409484896798707336367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37395758626391463219563645 14023409484896798707336367)
      ·
        refine ⟨21035114227345198061004551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14023409484896798707336367 21035114227345198061004551)
        ·
          refine ⟨31552671341017797091506827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21035114227345198061004551 31552671341017797091506827)
          ·
            refine ⟨47329007011526695637260241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31552671341017797091506827 47329007011526695637260241)
            ·
              refine ⟨35496755258645021727945181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47329007011526695637260241 35496755258645021727945181)
              ·
                refine ⟨13311283221991883147979443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35496755258645021727945181 13311283221991883147979443)
                ·
                  refine ⟨19966924832987824721969165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13311283221991883147979443 19966924832987824721969165)
                  ·
                    refine ⟨7487596812370434270738437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19966924832987824721969165 7487596812370434270738437)
                    ·
                      refine ⟨1403924402319456425763457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7487596812370434270738437 1403924402319456425763457)
                      ·
                        rfl

theorem cell23_2734133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2734133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734133 prefixEnd_2734133 := by exact prefixLift 2734133
  have htrace : WordTrace (prefixWord ++ tailWord_2734133) baseStart_2734133 baseEnd_2734133 := by
    simpa [prefixWord, tailWord_2734133, baseEnd_2734133] using wordTrace_append hprefix tailTrace_2734133
  have hstable : (prefixWord ++ tailWord_2734133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734133).length < 2 ^ (prefixWord ++ tailWord_2734133).sum := by decide
  have hdescent : baseEnd_2734133 < baseStart_2734133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734194 : List Nat := [3, 2, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_2734194 : Nat := 118140960795 + 2734194 * 2 ^ 59
def prefixEnd_2734194 : Nat := 4983230072969 + 3 ^ 40 * 2734194 * 2
def baseEnd_2734194 : Nat := 467985241546460229033559

theorem tailTrace_2734194 : CollatzResearch.WordTrace tailWord_2734194 prefixEnd_2734194 467985241546460229033559 := by
  unfold tailWord_2734194
  simp only [CollatzResearch.WordTrace]
  refine ⟨24931061964122394000868409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66482831904326384002315757 24931061964122394000868409)
  ·
    refine ⟨18698296473091795500651307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24931061964122394000868409 18698296473091795500651307)
    ·
      refine ⟨28047444709637693250976961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18698296473091795500651307 28047444709637693250976961)
      ·
        refine ⟨21035583532228269938232721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28047444709637693250976961 21035583532228269938232721)
        ·
          refine ⟨15776687649171202453674541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21035583532228269938232721 15776687649171202453674541)
          ·
            refine ⟨5916257868439200920127953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15776687649171202453674541 5916257868439200920127953)
            ·
              refine ⟨4437193401329400690095965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5916257868439200920127953 4437193401329400690095965)
              ·
                refine ⟨1663947525498525258785987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4437193401329400690095965 1663947525498525258785987)
                ·
                  refine ⟨2495921288247787888178981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663947525498525258785987 2495921288247787888178981)
                  ·
                    refine ⟨467985241546460229033559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495921288247787888178981 467985241546460229033559)
                    ·
                      rfl

theorem cell23_2734194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_2734194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734194 prefixEnd_2734194 := by exact prefixLift 2734194
  have htrace : WordTrace (prefixWord ++ tailWord_2734194) baseStart_2734194 baseEnd_2734194 := by
    simpa [prefixWord, tailWord_2734194, baseEnd_2734194] using wordTrace_append hprefix tailTrace_2734194
  have hstable : (prefixWord ++ tailWord_2734194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734194).length < 2 ^ (prefixWord ++ tailWord_2734194).sum := by decide
  have hdescent : baseEnd_2734194 < baseStart_2734194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734200 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 7, 1, 3]
def baseStart_2734200 : Nat := 118140960795 + 2734200 * 2 ^ 59
def prefixEnd_2734200 : Nat := 4983230072969 + 3 ^ 40 * 2734200 * 2
def baseEnd_2734200 : Nat := 1403958805523307663625649

theorem tailTrace_2734200 : CollatzResearch.WordTrace tailWord_2734200 prefixEnd_2734200 1403958805523307663625649 := by
  unfold tailWord_2734200
  simp only [CollatzResearch.WordTrace]
  refine ⟨49862233347233919514096027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66482977796311892685461369 49862233347233919514096027)
  ·
    refine ⟨74793350020850879271144041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49862233347233919514096027 74793350020850879271144041)
    ·
      refine ⟨56095012515638159453358031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74793350020850879271144041 56095012515638159453358031)
      ·
        refine ⟨84142518773457239180037047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56095012515638159453358031 84142518773457239180037047)
        ·
          refine ⟨126213778160185858770055571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84142518773457239180037047 126213778160185858770055571)
          ·
            refine ⟨189320667240278788155083357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126213778160185858770055571 189320667240278788155083357)
            ·
              refine ⟨70995250215104545558156259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189320667240278788155083357 70995250215104545558156259)
              ·
                refine ⟨106492875322656818337234389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70995250215104545558156259 106492875322656818337234389)
                ·
                  refine ⟨2495926765374769179778931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 106492875322656818337234389 2495926765374769179778931)
                  ·
                    refine ⟨3743890148062153769668397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2495926765374769179778931 3743890148062153769668397)
                    ·
                      refine ⟨1403958805523307663625649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3743890148062153769668397 1403958805523307663625649)
                      ·
                        rfl

theorem cell23_2734200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_2734200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734200 prefixEnd_2734200 := by exact prefixLift 2734200
  have htrace : WordTrace (prefixWord ++ tailWord_2734200) baseStart_2734200 baseEnd_2734200 := by
    simpa [prefixWord, tailWord_2734200, baseEnd_2734200] using wordTrace_append hprefix tailTrace_2734200
  have hstable : (prefixWord ++ tailWord_2734200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734200).length < 2 ^ (prefixWord ++ tailWord_2734200).sum := by decide
  have hdescent : baseEnd_2734200 < baseStart_2734200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734217 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 3]
def baseStart_2734217 : Nat := 118140960795 + 2734217 * 2 ^ 59
def prefixEnd_2734217 : Nat := 4983230072969 + 3 ^ 40 * 2734217 * 2
def baseEnd_2734217 : Nat := 1403967534694434097113071

theorem tailTrace_2734217 : CollatzResearch.WordTrace tailWord_2734217 prefixEnd_2734217 1403967534694434097113071 := by
  unfold tailWord_2734217
  simp only [CollatzResearch.WordTrace]
  refine ⟨99725086735406250931560905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66483391156937500621040603 99725086735406250931560905)
  ·
    refine ⟨74793815051554688198670679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99725086735406250931560905 74793815051554688198670679)
    ·
      refine ⟨112190722577332032298006019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74793815051554688198670679 112190722577332032298006019)
      ·
        refine ⟨168286083865998048447009029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112190722577332032298006019 168286083865998048447009029)
        ·
          refine ⟨31553640724874634083814193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168286083865998048447009029 31553640724874634083814193)
          ·
            refine ⟨23665230543655975562860645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31553640724874634083814193 23665230543655975562860645)
            ·
              refine ⟨4437230726935495418036371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23665230543655975562860645 4437230726935495418036371)
              ·
                refine ⟨6655846090403243127054557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437230726935495418036371 6655846090403243127054557)
                ·
                  refine ⟨2495942283901216172645459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6655846090403243127054557 2495942283901216172645459)
                  ·
                    refine ⟨3743913425851824258968189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2495942283901216172645459 3743913425851824258968189)
                    ·
                      refine ⟨1403967534694434097113071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3743913425851824258968189 1403967534694434097113071)
                      ·
                        rfl

theorem cell23_2734217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 3].length) (baseStart_2734217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734217 prefixEnd_2734217 := by exact prefixLift 2734217
  have htrace : WordTrace (prefixWord ++ tailWord_2734217) baseStart_2734217 baseEnd_2734217 := by
    simpa [prefixWord, tailWord_2734217, baseEnd_2734217] using wordTrace_append hprefix tailTrace_2734217
  have hstable : (prefixWord ++ tailWord_2734217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734217).length < 2 ^ (prefixWord ++ tailWord_2734217).sum := by decide
  have hdescent : baseEnd_2734217 < baseStart_2734217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734237 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2734237 : Nat := 118140960795 + 2734237 * 2 ^ 59
def prefixEnd_2734237 : Nat := 4983230072969 + 3 ^ 40 * 2734237 * 2
def baseEnd_2734237 : Nat := 467992601435841339620993

theorem tailTrace_2734237 : CollatzResearch.WordTrace tailWord_2734237 prefixEnd_2734237 467992601435841339620993 := by
  unfold tailWord_2734237
  simp only [CollatzResearch.WordTrace]
  refine ⟨99725816195333794347288965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66483877463555862898192643 99725816195333794347288965)
  ·
    refine ⟨18698590536625086440116681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99725816195333794347288965 18698590536625086440116681)
    ·
      refine ⟨14023942902468814830087511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18698590536625086440116681 14023942902468814830087511)
      ·
        refine ⟨21035914353703222245131267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14023942902468814830087511 21035914353703222245131267)
        ·
          refine ⟨31553871530554833367696901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21035914353703222245131267 31553871530554833367696901)
          ·
            refine ⟨5916350911979031256443169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31553871530554833367696901 5916350911979031256443169)
            ·
              refine ⟨4437263183984273442332377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5916350911979031256443169 4437263183984273442332377)
              ·
                refine ⟨3327947387988205081749283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4437263183984273442332377 3327947387988205081749283)
                ·
                  refine ⟨4991921081982307622623925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327947387988205081749283 4991921081982307622623925)
                  ·
                    refine ⟨467992601435841339620993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4991921081982307622623925 467992601435841339620993)
                    ·
                      rfl

theorem cell23_2734237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2734237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734237 prefixEnd_2734237 := by exact prefixLift 2734237
  have htrace : WordTrace (prefixWord ++ tailWord_2734237) baseStart_2734237 baseEnd_2734237 := by
    simpa [prefixWord, tailWord_2734237, baseEnd_2734237] using wordTrace_append hprefix tailTrace_2734237
  have hstable : (prefixWord ++ tailWord_2734237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734237).length < 2 ^ (prefixWord ++ tailWord_2734237).sum := by decide
  have hdescent : baseEnd_2734237 < baseStart_2734237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734261 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_2734261 : Nat := 118140960795 + 2734261 * 2 ^ 59
def prefixEnd_2734261 : Nat := 4983230072969 + 3 ^ 40 * 2734261 * 2
def baseEnd_2734261 : Nat := 1403990127843231924962869

theorem tailTrace_2734261 : CollatzResearch.WordTrace tailWord_2734261 prefixEnd_2734261 1403990127843231924962869 := by
  unfold tailWord_2734261
  simp only [CollatzResearch.WordTrace]
  refine ⟨99726691547246846446162637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66484461031497897630775091 99726691547246846446162637)
  ·
    refine ⟨37397509330217567417310989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99726691547246846446162637 37397509330217567417310989)
    ·
      refine ⟨14024065998831587781491621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37397509330217567417310989 14024065998831587781491621)
      ·
        refine ⟨2629512374780922709029679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14024065998831587781491621 2629512374780922709029679)
        ·
          refine ⟨3944268562171384063544519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2629512374780922709029679 3944268562171384063544519)
          ·
            refine ⟨5916402843257076095316779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3944268562171384063544519 5916402843257076095316779)
            ·
              refine ⟨8874604264885614142975169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5916402843257076095316779 8874604264885614142975169)
              ·
                refine ⟨6655953198664210607231377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8874604264885614142975169 6655953198664210607231377)
                ·
                  refine ⟨4991964898998157955423533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6655953198664210607231377 4991964898998157955423533)
                  ·
                    refine ⟨1871986837124309233283825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4991964898998157955423533 1871986837124309233283825)
                    ·
                      refine ⟨1403990127843231924962869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1871986837124309233283825 1403990127843231924962869)
                      ·
                        rfl

theorem cell23_2734261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_2734261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734261 prefixEnd_2734261 := by exact prefixLift 2734261
  have htrace : WordTrace (prefixWord ++ tailWord_2734261) baseStart_2734261 baseEnd_2734261 := by
    simpa [prefixWord, tailWord_2734261, baseEnd_2734261] using wordTrace_append hprefix tailTrace_2734261
  have hstable : (prefixWord ++ tailWord_2734261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734261).length < 2 ^ (prefixWord ++ tailWord_2734261).sum := by decide
  have hdescent : baseEnd_2734261 < baseStart_2734261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734263 : List Nat := [1, 1, 3, 1, 4, 2, 11]
def baseStart_2734263 : Nat := 118140960795 + 2734263 * 2 ^ 59
def prefixEnd_2734263 : Nat := 4983230072969 + 3 ^ 40 * 2734263 * 2
def baseEnd_2734263 : Nat := 17333224133389394038739

theorem tailTrace_2734263 : CollatzResearch.WordTrace tailWord_2734263 prefixEnd_2734263 17333224133389394038739 := by
  unfold tailWord_2734263
  simp only [CollatzResearch.WordTrace]
  refine ⟨99726764493239600787735443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66484509662159733858490295 99726764493239600787735443)
  ·
    refine ⟨149590146739859401181603165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99726764493239600787735443 149590146739859401181603165)
    ·
      refine ⟨56096305027447275443101187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149590146739859401181603165 56096305027447275443101187)
      ·
        refine ⟨84144457541170913164651781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56096305027447275443101187 84144457541170913164651781)
        ·
          refine ⟨15777085788969546218372209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84144457541170913164651781 15777085788969546218372209)
          ·
            refine ⟨11832814341727159663779157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15777085788969546218372209 11832814341727159663779157)
            ·
              refine ⟨17333224133389394038739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11832814341727159663779157 17333224133389394038739)
              ·
                rfl

theorem cell23_2734263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 11].length) (baseStart_2734263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734263 prefixEnd_2734263 := by exact prefixLift 2734263
  have htrace : WordTrace (prefixWord ++ tailWord_2734263) baseStart_2734263 baseEnd_2734263 := by
    simpa [prefixWord, tailWord_2734263, baseEnd_2734263] using wordTrace_append hprefix tailTrace_2734263
  have hstable : (prefixWord ++ tailWord_2734263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734263).length < 2 ^ (prefixWord ++ tailWord_2734263).sum := by decide
  have hdescent : baseEnd_2734263 < baseStart_2734263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734268 : List Nat := [2, 2, 2, 3, 3, 1, 3, 2, 1, 1, 3]
def baseStart_2734268 : Nat := 118140960795 + 2734268 * 2 ^ 59
def prefixEnd_2734268 : Nat := 4983230072969 + 3 ^ 40 * 2734268 * 2
def baseEnd_2734268 : Nat := 1403993722207813397575337

theorem tailTrace_2734268 : CollatzResearch.WordTrace tailWord_2734268 prefixEnd_2734268 1403993722207813397575337 := by
  unfold tailWord_2734268
  simp only [CollatzResearch.WordTrace]
  refine ⟨49863473429110743320833729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66484631238814324427778305 49863473429110743320833729)
  ·
    refine ⟨37397605071833057490625297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49863473429110743320833729 37397605071833057490625297)
    ·
      refine ⟨28048203803874793117968973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37397605071833057490625297 28048203803874793117968973)
      ·
        refine ⟨10518076426453047419238365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28048203803874793117968973 10518076426453047419238365)
        ·
          refine ⟨3944278659919892782214387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10518076426453047419238365 3944278659919892782214387)
          ·
            refine ⟨5916417989879839173321581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3944278659919892782214387 5916417989879839173321581)
            ·
              refine ⟨2218656746204939689995593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5916417989879839173321581 2218656746204939689995593)
              ·
                refine ⟨1663992559653704767496695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2218656746204939689995593 1663992559653704767496695)
                ·
                  refine ⟨2495988839480557151245043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663992559653704767496695 2495988839480557151245043)
                  ·
                    refine ⟨3743983259220835726867565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2495988839480557151245043 3743983259220835726867565)
                    ·
                      refine ⟨1403993722207813397575337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3743983259220835726867565 1403993722207813397575337)
                      ·
                        rfl

theorem cell23_2734268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_2734268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734268 prefixEnd_2734268 := by exact prefixLift 2734268
  have htrace : WordTrace (prefixWord ++ tailWord_2734268) baseStart_2734268 baseEnd_2734268 := by
    simpa [prefixWord, tailWord_2734268, baseEnd_2734268] using wordTrace_append hprefix tailTrace_2734268
  have hstable : (prefixWord ++ tailWord_2734268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734268).length < 2 ^ (prefixWord ++ tailWord_2734268).sum := by decide
  have hdescent : baseEnd_2734268 < baseStart_2734268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734283 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 6]
def baseStart_2734283 : Nat := 118140960795 + 2734283 * 2 ^ 59
def prefixEnd_2734283 : Nat := 4983230072969 + 3 ^ 40 * 2734283 * 2
def baseEnd_2734283 : Nat := 1404001424417630838887767

theorem tailTrace_2734283 : CollatzResearch.WordTrace tailWord_2734283 prefixEnd_2734283 1404001424417630838887767 := by
  unfold tailWord_2734283
  simp only [CollatzResearch.WordTrace]
  refine ⟨99727493953167144203463503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66484995968778096135642335 99727493953167144203463503)
  ·
    refine ⟨149591240929750716305195255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99727493953167144203463503 149591240929750716305195255)
    ·
      refine ⟨224386861394626074457792883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149591240929750716305195255 224386861394626074457792883)
      ·
        refine ⟨336580292091939111686689325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224386861394626074457792883 336580292091939111686689325)
        ·
          refine ⟨126217609534477166882508497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336580292091939111686689325 126217609534477166882508497)
          ·
            refine ⟨94663207150857875161881373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126217609534477166882508497 94663207150857875161881373)
            ·
              refine ⟨35498702681571703185705515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94663207150857875161881373 35498702681571703185705515)
              ·
                refine ⟨53248054022357554778558273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35498702681571703185705515 53248054022357554778558273)
                ·
                  refine ⟨39936040516768166083918705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53248054022357554778558273 39936040516768166083918705)
                  ·
                    refine ⟨29952030387576124562939029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39936040516768166083918705 29952030387576124562939029)
                    ·
                      refine ⟨1404001424417630838887767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29952030387576124562939029 1404001424417630838887767)
                      ·
                        rfl

theorem cell23_2734283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_2734283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734283 prefixEnd_2734283 := by exact prefixLift 2734283
  have htrace : WordTrace (prefixWord ++ tailWord_2734283) baseStart_2734283 baseEnd_2734283 := by
    simpa [prefixWord, tailWord_2734283, baseEnd_2734283] using wordTrace_append hprefix tailTrace_2734283
  have hstable : (prefixWord ++ tailWord_2734283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734283).length < 2 ^ (prefixWord ++ tailWord_2734283).sum := by decide
  have hdescent : baseEnd_2734283 < baseStart_2734283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734311 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2734311 : Nat := 118140960795 + 2734311 * 2 ^ 59
def prefixEnd_2734311 : Nat := 4983230072969 + 3 ^ 40 * 2734311 * 2
def baseEnd_2734311 : Nat := 1404015801875956729337639

theorem tailTrace_2734311 : CollatzResearch.WordTrace tailWord_2734311 prefixEnd_2734311 1404015801875956729337639 := by
  unfold tailWord_2734311
  simp only [CollatzResearch.WordTrace]
  refine ⟨99728515197065704985482787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66485676798043803323655191 99728515197065704985482787)
  ·
    refine ⟨149592772795598557478224181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99728515197065704985482787 149592772795598557478224181)
    ·
      refine ⟨14024322449587364763583517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149592772795598557478224181 14024322449587364763583517)
      ·
        refine ⟨5259120918595261786343819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14024322449587364763583517 5259120918595261786343819)
        ·
          refine ⟨7888681377892892679515729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259120918595261786343819 7888681377892892679515729)
          ·
            refine ⟨5916511033419669509636797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7888681377892892679515729 5916511033419669509636797)
            ·
              refine ⟨2218691637532376066113799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5916511033419669509636797 2218691637532376066113799)
              ·
                refine ⟨3328037456298564099170699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2218691637532376066113799 3328037456298564099170699)
                ·
                  refine ⟨4992056184447846148756049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3328037456298564099170699 4992056184447846148756049)
                  ·
                    refine ⟨3744042138335884611567037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4992056184447846148756049 3744042138335884611567037)
                    ·
                      refine ⟨1404015801875956729337639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3744042138335884611567037 1404015801875956729337639)
                      ·
                        rfl

theorem cell23_2734311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2734311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734311 prefixEnd_2734311 := by exact prefixLift 2734311
  have htrace : WordTrace (prefixWord ++ tailWord_2734311) baseStart_2734311 baseEnd_2734311 := by
    simpa [prefixWord, tailWord_2734311, baseEnd_2734311] using wordTrace_append hprefix tailTrace_2734311
  have hstable : (prefixWord ++ tailWord_2734311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734311).length < 2 ^ (prefixWord ++ tailWord_2734311).sum := by decide
  have hdescent : baseEnd_2734311 < baseStart_2734311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734313 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_2734313 : Nat := 118140960795 + 2734313 * 2 ^ 59
def prefixEnd_2734313 : Nat := 4983230072969 + 3 ^ 40 * 2734313 * 2
def baseEnd_2734313 : Nat := 1404016828837265721512629

theorem tailTrace_2734313 : CollatzResearch.WordTrace tailWord_2734313 prefixEnd_2734313 1404016828837265721512629 := by
  unfold tailWord_2734313
  simp only [CollatzResearch.WordTrace]
  refine ⟨99728588143058459327055593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66485725428705639551370395 99728588143058459327055593)
  ·
    refine ⟨74796441107293844495291695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99728588143058459327055593 74796441107293844495291695)
    ·
      refine ⟨112194661660940766742937543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74796441107293844495291695 112194661660940766742937543)
      ·
        refine ⟨168291992491411150114406315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112194661660940766742937543 168291992491411150114406315)
        ·
          refine ⟨252437988737116725171609473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168291992491411150114406315 252437988737116725171609473)
          ·
            refine ⟨189328491552837543878707105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252437988737116725171609473 189328491552837543878707105)
            ·
              refine ⟨141996368664628157909030329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189328491552837543878707105 141996368664628157909030329)
              ·
                refine ⟨106497276498471118431772747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141996368664628157909030329 106497276498471118431772747)
                ·
                  refine ⟨159745914747706677647659121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106497276498471118431772747 159745914747706677647659121)
                  ·
                    refine ⟨119809436060780008235744341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159745914747706677647659121 119809436060780008235744341)
                    ·
                      refine ⟨1404016828837265721512629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 119809436060780008235744341 1404016828837265721512629)
                      ·
                        rfl

theorem cell23_2734313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_2734313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734313 prefixEnd_2734313 := by exact prefixLift 2734313
  have htrace : WordTrace (prefixWord ++ tailWord_2734313) baseStart_2734313 baseEnd_2734313 := by
    simpa [prefixWord, tailWord_2734313, baseEnd_2734313] using wordTrace_append hprefix tailTrace_2734313
  have hstable : (prefixWord ++ tailWord_2734313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734313).length < 2 ^ (prefixWord ++ tailWord_2734313).sum := by decide
  have hdescent : baseEnd_2734313 < baseStart_2734313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734330 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_2734330 : Nat := 118140960795 + 2734330 * 2 ^ 59
def prefixEnd_2734330 : Nat := 4983230072969 + 3 ^ 40 * 2734330 * 2
def baseEnd_2734330 : Nat := 1404025558008392155000051

theorem tailTrace_2734330 : CollatzResearch.WordTrace tailWord_2734330 prefixEnd_2734330 1404025558008392155000051 := by
  unfold tailWord_2734330
  simp only [CollatzResearch.WordTrace]
  refine ⟨24932302045999217807606111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66486138789331247486949629 24932302045999217807606111)
  ·
    refine ⟨37398453068998826711409167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24932302045999217807606111 37398453068998826711409167)
    ·
      refine ⟨56097679603498240067113751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37398453068998826711409167 56097679603498240067113751)
      ·
        refine ⟨84146519405247360100670627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56097679603498240067113751 84146519405247360100670627)
        ·
          refine ⟨126219779107871040151005941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84146519405247360100670627 126219779107871040151005941)
          ·
            refine ⟨11833104291362910014156807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126219779107871040151005941 11833104291362910014156807)
            ·
              refine ⟨17749656437044365021235211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11833104291362910014156807 17749656437044365021235211)
              ·
                refine ⟨26624484655566547531852817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17749656437044365021235211 26624484655566547531852817)
                ·
                  refine ⟨19968363491674910648889613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26624484655566547531852817 19968363491674910648889613)
                  ·
                    refine ⟨7488136309378091493333605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19968363491674910648889613 7488136309378091493333605)
                    ·
                      refine ⟨1404025558008392155000051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7488136309378091493333605 1404025558008392155000051)
                      ·
                        rfl

theorem cell23_2734330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_2734330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734330 prefixEnd_2734330 := by exact prefixLift 2734330
  have htrace : WordTrace (prefixWord ++ tailWord_2734330) baseStart_2734330 baseEnd_2734330 := by
    simpa [prefixWord, tailWord_2734330, baseEnd_2734330] using wordTrace_append hprefix tailTrace_2734330
  have hstable : (prefixWord ++ tailWord_2734330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734330).length < 2 ^ (prefixWord ++ tailWord_2734330).sum := by decide
  have hdescent : baseEnd_2734330 < baseStart_2734330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734334 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_2734334 : Nat := 118140960795 + 2734334 * 2 ^ 59
def prefixEnd_2734334 : Nat := 4983230072969 + 3 ^ 40 * 2734334 * 2
def baseEnd_2734334 : Nat := 1404027611931010139350033

theorem tailTrace_2734334 : CollatzResearch.WordTrace tailWord_2734334 prefixEnd_2734334 1404027611931010139350033 := by
  unfold tailWord_2734334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12466169259497797489196257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66486236050654919942380037 12466169259497797489196257)
  ·
    refine ⟨9349626944623348116897193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12466169259497797489196257 9349626944623348116897193)
    ·
      refine ⟨7012220208467511087672895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9349626944623348116897193 7012220208467511087672895)
      ·
        refine ⟨10518330312701266631509343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7012220208467511087672895 10518330312701266631509343)
        ·
          refine ⟨15777495469051899947264015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10518330312701266631509343 15777495469051899947264015)
          ·
            refine ⟨23666243203577849920896023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15777495469051899947264015 23666243203577849920896023)
            ·
              refine ⟨35499364805366774881344035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23666243203577849920896023 35499364805366774881344035)
              ·
                refine ⟨53249047208050162322016053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35499364805366774881344035 53249047208050162322016053)
                ·
                  refine ⟨4992098175754702717689005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53249047208050162322016053 4992098175754702717689005)
                  ·
                    refine ⟨1872036815908013519133377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4992098175754702717689005 1872036815908013519133377)
                    ·
                      refine ⟨1404027611931010139350033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872036815908013519133377 1404027611931010139350033)
                      ·
                        rfl

theorem cell23_2734334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_2734334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734334 prefixEnd_2734334 := by exact prefixLift 2734334
  have htrace : WordTrace (prefixWord ++ tailWord_2734334) baseStart_2734334 baseEnd_2734334 := by
    simpa [prefixWord, tailWord_2734334, baseEnd_2734334] using wordTrace_append hprefix tailTrace_2734334
  have hstable : (prefixWord ++ tailWord_2734334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734334).length < 2 ^ (prefixWord ++ tailWord_2734334).sum := by decide
  have hdescent : baseEnd_2734334 < baseStart_2734334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734360 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2734360 : Nat := 118140960795 + 2734360 * 2 ^ 59
def prefixEnd_2734360 : Nat := 4983230072969 + 3 ^ 40 * 2734360 * 2
def baseEnd_2734360 : Nat := 1404040962428027037624913

theorem tailTrace_2734360 : CollatzResearch.WordTrace tailWord_2734360 prefixEnd_2734360 1404040962428027037624913 := by
  unfold tailWord_2734360
  simp only [CollatzResearch.WordTrace]
  refine ⟨49865151186944093177008267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66486868249258790902677689 49865151186944093177008267)
  ·
    refine ⟨74797726780416139765512401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49865151186944093177008267 74797726780416139765512401)
    ·
      refine ⟨56098295085312104824134301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74797726780416139765512401 56098295085312104824134301)
      ·
        refine ⟨21036860656992039309050363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56098295085312104824134301 21036860656992039309050363)
        ·
          refine ⟨31555290985488058963575545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21036860656992039309050363 31555290985488058963575545)
          ·
            refine ⟨23666468239116044222681659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31555290985488058963575545 23666468239116044222681659)
            ·
              refine ⟨35499702358674066334022489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23666468239116044222681659 35499702358674066334022489)
              ·
                refine ⟨26624776769005549750516867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35499702358674066334022489 26624776769005549750516867)
                ·
                  refine ⟨39937165153508324625775301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26624776769005549750516867 39937165153508324625775301)
                  ·
                    refine ⟨7488218466282810867332869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39937165153508324625775301 7488218466282810867332869)
                    ·
                      refine ⟨1404040962428027037624913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7488218466282810867332869 1404040962428027037624913)
                      ·
                        rfl

theorem cell23_2734360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2734360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734360 prefixEnd_2734360 := by exact prefixLift 2734360
  have htrace : WordTrace (prefixWord ++ tailWord_2734360) baseStart_2734360 baseEnd_2734360 := by
    simpa [prefixWord, tailWord_2734360, baseEnd_2734360] using wordTrace_append hprefix tailTrace_2734360
  have hstable : (prefixWord ++ tailWord_2734360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734360).length < 2 ^ (prefixWord ++ tailWord_2734360).sum := by decide
  have hdescent : baseEnd_2734360 < baseStart_2734360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734364 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_2734364 : Nat := 118140960795 + 2734364 * 2 ^ 59
def prefixEnd_2734364 : Nat := 4983230072969 + 3 ^ 40 * 2734364 * 2
def baseEnd_2734364 : Nat := 1404043016350645021974895

theorem tailTrace_2734364 : CollatzResearch.WordTrace tailWord_2734364 prefixEnd_2734364 1404043016350645021974895 := by
  unfold tailWord_2734364
  simp only [CollatzResearch.WordTrace]
  refine ⟨49865224132936847518581073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66486965510582463358108097 49865224132936847518581073)
  ·
    refine ⟨37398918099702635638935805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49865224132936847518581073 37398918099702635638935805)
    ·
      refine ⟨14024594287388488364600927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37398918099702635638935805 14024594287388488364600927)
      ·
        refine ⟨21036891431082732546901391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14024594287388488364600927 21036891431082732546901391)
        ·
          refine ⟨31555337146624098820352087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21036891431082732546901391 31555337146624098820352087)
          ·
            refine ⟨47333005719936148230528131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31555337146624098820352087 47333005719936148230528131)
            ·
              refine ⟨70999508579904222345792197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47333005719936148230528131 70999508579904222345792197)
              ·
                refine ⟨13312407858732041689836037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70999508579904222345792197 13312407858732041689836037)
                ·
                  refine ⟨2496076473512257816844257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13312407858732041689836037 2496076473512257816844257)
                  ·
                    refine ⟨1872057355134193362633193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2496076473512257816844257 1872057355134193362633193)
                    ·
                      refine ⟨1404043016350645021974895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872057355134193362633193 1404043016350645021974895)
                      ·
                        rfl

theorem cell23_2734364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_2734364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734364 prefixEnd_2734364 := by exact prefixLift 2734364
  have htrace : WordTrace (prefixWord ++ tailWord_2734364) baseStart_2734364 baseEnd_2734364 := by
    simpa [prefixWord, tailWord_2734364, baseEnd_2734364] using wordTrace_append hprefix tailTrace_2734364
  have hstable : (prefixWord ++ tailWord_2734364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734364).length < 2 ^ (prefixWord ++ tailWord_2734364).sum := by decide
  have hdescent : baseEnd_2734364 < baseStart_2734364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734368 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 1, 3, 2]
def baseStart_2734368 : Nat := 118140960795 + 2734368 * 2 ^ 59
def prefixEnd_2734368 : Nat := 4983230072969 + 3 ^ 40 * 2734368 * 2
def baseEnd_2734368 : Nat := 1404045070273263006324877

theorem tailTrace_2734368 : CollatzResearch.WordTrace tailWord_2734368 prefixEnd_2734368 1404045070273263006324877 := by
  unfold tailWord_2734368
  simp only [CollatzResearch.WordTrace]
  refine ⟨49865297078929601860153879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66487062771906135813538505 49865297078929601860153879)
  ·
    refine ⟨74797945618394402790230819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49865297078929601860153879 74797945618394402790230819)
    ·
      refine ⟨112196918427591604185346229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74797945618394402790230819 112196918427591604185346229)
      ·
        refine ⟨10518461102586712892376209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112196918427591604185346229 10518461102586712892376209)
        ·
          refine ⟨7888845826940034669282157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10518461102586712892376209 7888845826940034669282157)
          ·
            refine ⟨2958317185102513000980809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7888845826940034669282157 2958317185102513000980809)
            ·
              refine ⟨2218737888826884750735607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2958317185102513000980809 2218737888826884750735607)
              ·
                refine ⟨3328106833240327126103411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2218737888826884750735607 3328106833240327126103411)
                ·
                  refine ⟨4992160249860490689155117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3328106833240327126103411 4992160249860490689155117)
                  ·
                    refine ⟨1872060093697684008433169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4992160249860490689155117 1872060093697684008433169)
                    ·
                      refine ⟨1404045070273263006324877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872060093697684008433169 1404045070273263006324877)
                      ·
                        rfl

theorem cell23_2734368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_2734368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734368 prefixEnd_2734368 := by exact prefixLift 2734368
  have htrace : WordTrace (prefixWord ++ tailWord_2734368) baseStart_2734368 baseEnd_2734368 := by
    simpa [prefixWord, tailWord_2734368, baseEnd_2734368] using wordTrace_append hprefix tailTrace_2734368
  have hstable : (prefixWord ++ tailWord_2734368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734368).length < 2 ^ (prefixWord ++ tailWord_2734368).sum := by decide
  have hdescent : baseEnd_2734368 < baseStart_2734368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734387 : List Nat := [1, 1, 1, 2, 5, 1, 1, 6, 5]
def baseStart_2734387 : Nat := 118140960795 + 2734387 * 2 ^ 59
def prefixEnd_2734387 : Nat := 4983230072969 + 3 ^ 40 * 2734387 * 2
def baseEnd_2734387 : Nat := 156006091822855381331921

theorem tailTrace_2734387 : CollatzResearch.WordTrace tailWord_2734387 prefixEnd_2734387 156006091822855381331921 := by
  unfold tailWord_2734387
  simp only [CollatzResearch.WordTrace]
  refine ⟨99731287144790369965249415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66487524763193579976832943 99731287144790369965249415)
  ·
    refine ⟨149596930717185554947874123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99731287144790369965249415 149596930717185554947874123)
    ·
      refine ⟨224395396075778332421811185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149596930717185554947874123 224395396075778332421811185)
      ·
        refine ⟨168296547056833749316358389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224395396075778332421811185 168296547056833749316358389)
        ·
          refine ⟨15777801286578163998408599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168296547056833749316358389 15777801286578163998408599)
          ·
            refine ⟨23666701929867245997612899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15777801286578163998408599 23666701929867245997612899)
            ·
              refine ⟨35500052894800868996419349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23666701929867245997612899 35500052894800868996419349)
              ·
                refine ⟨1664064979443790734207157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35500052894800868996419349 1664064979443790734207157)
                ·
                  refine ⟨156006091822855381331921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1664064979443790734207157 156006091822855381331921)
                  ·
                    rfl

theorem cell23_2734387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 5].length) (baseStart_2734387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734387 prefixEnd_2734387 := by exact prefixLift 2734387
  have htrace : WordTrace (prefixWord ++ tailWord_2734387) baseStart_2734387 baseEnd_2734387 := by
    simpa [prefixWord, tailWord_2734387, baseEnd_2734387] using wordTrace_append hprefix tailTrace_2734387
  have hstable : (prefixWord ++ tailWord_2734387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734387).length < 2 ^ (prefixWord ++ tailWord_2734387).sum := by decide
  have hdescent : baseEnd_2734387 < baseStart_2734387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734400 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 6, 5]
def baseStart_2734400 : Nat := 118140960795 + 2734400 * 2 ^ 59
def prefixEnd_2734400 : Nat := 4983230072969 + 3 ^ 40 * 2734400 * 2
def baseEnd_2734400 : Nat := 468020500551402293708243

theorem tailTrace_2734400 : CollatzResearch.WordTrace tailWord_2734400 prefixEnd_2734400 468020500551402293708243 := by
  unfold tailWord_2734400
  simp only [CollatzResearch.WordTrace]
  refine ⟨49865880646871636592736327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66487840862495515456981769 49865880646871636592736327)
  ·
    refine ⟨74798820970307454889104491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49865880646871636592736327 74798820970307454889104491)
    ·
      refine ⟨112198231455461182333656737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74798820970307454889104491 112198231455461182333656737)
      ·
        refine ⟨84148673591595886750242553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112198231455461182333656737 84148673591595886750242553)
        ·
          refine ⟨63111505193696915062681915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84148673591595886750242553 63111505193696915062681915)
          ·
            refine ⟨94667257790545372594022873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63111505193696915062681915 94667257790545372594022873)
            ·
              refine ⟨71000443342909029445517155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94667257790545372594022873 71000443342909029445517155)
              ·
                refine ⟨106500665014363544168275733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71000443342909029445517155 106500665014363544168275733)
                ·
                  refine ⟨4992218672548291132887925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106500665014363544168275733 4992218672548291132887925)
                  ·
                    refine ⟨468020500551402293708243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4992218672548291132887925 468020500551402293708243)
                    ·
                      rfl

theorem cell23_2734400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_2734400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734400 prefixEnd_2734400 := by exact prefixLift 2734400
  have htrace : WordTrace (prefixWord ++ tailWord_2734400) baseStart_2734400 baseEnd_2734400 := by
    simpa [prefixWord, tailWord_2734400, baseEnd_2734400] using wordTrace_append hprefix tailTrace_2734400
  have hstable : (prefixWord ++ tailWord_2734400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734400).length < 2 ^ (prefixWord ++ tailWord_2734400).sum := by decide
  have hdescent : baseEnd_2734400 < baseStart_2734400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734410 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_2734410 : Nat := 118140960795 + 2734410 * 2 ^ 59
def prefixEnd_2734410 : Nat := 4983230072969 + 3 ^ 40 * 2734410 * 2
def baseEnd_2734410 : Nat := 1404066636460751841999683

theorem tailTrace_2734410 : CollatzResearch.WordTrace tailWord_2734410 prefixEnd_2734410 1404066636460751841999683 := by
  unfold tailWord_2734410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24933031505926761223334171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66488084015804696595557789 24933031505926761223334171)
  ·
    refine ⟨37399547258890141835001257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24933031505926761223334171 37399547258890141835001257)
    ·
      refine ⟨28049660444167606376250943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37399547258890141835001257 28049660444167606376250943)
      ·
        refine ⟨42074490666251409564376415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28049660444167606376250943 42074490666251409564376415)
        ·
          refine ⟨63111735999377114346564623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42074490666251409564376415 63111735999377114346564623)
          ·
            refine ⟨94667603999065671519846935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63111735999377114346564623 94667603999065671519846935)
            ·
              refine ⟨142001405998598507279770403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94667603999065671519846935 142001405998598507279770403)
              ·
                refine ⟨213002108997897760919655605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142001405998598507279770403 213002108997897760919655605)
                ·
                  refine ⟨19968947718552915086217713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213002108997897760919655605 19968947718552915086217713)
                  ·
                    refine ⟨14976710788914686314663285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19968947718552915086217713 14976710788914686314663285)
                    ·
                      refine ⟨1404066636460751841999683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14976710788914686314663285 1404066636460751841999683)
                      ·
                        rfl

theorem cell23_2734410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_2734410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734410 prefixEnd_2734410 := by exact prefixLift 2734410
  have htrace : WordTrace (prefixWord ++ tailWord_2734410) baseStart_2734410 baseEnd_2734410 := by
    simpa [prefixWord, tailWord_2734410, baseEnd_2734410] using wordTrace_append hprefix tailTrace_2734410
  have hstable : (prefixWord ++ tailWord_2734410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734410).length < 2 ^ (prefixWord ++ tailWord_2734410).sum := by decide
  have hdescent : baseEnd_2734410 < baseStart_2734410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734421 : List Nat := [1, 3, 2, 2, 4, 2, 1, 3, 5]
def baseStart_2734421 : Nat := 118140960795 + 2734421 * 2 ^ 59
def prefixEnd_2734421 : Nat := 4983230072969 + 3 ^ 40 * 2734421 * 2
def baseEnd_2734421 : Nat := 156008031638661255440237

theorem tailTrace_2734421 : CollatzResearch.WordTrace tailWord_2734421 prefixEnd_2734421 156008031638661255440237 := by
  unfold tailWord_2734421
  simp only [CollatzResearch.WordTrace]
  refine ⟨99732527226667193771987117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66488351484444795847991411 99732527226667193771987117)
  ·
    refine ⟨37399697710000197664495169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99732527226667193771987117 37399697710000197664495169)
    ·
      refine ⟨28049773282500148248371377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37399697710000197664495169 28049773282500148248371377)
      ·
        refine ⟨21037329961875111186278533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28049773282500148248371377 21037329961875111186278533)
        ·
          refine ⟨3944499367851583347427225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21037329961875111186278533 3944499367851583347427225)
          ·
            refine ⟨2958374525888687510570419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3944499367851583347427225 2958374525888687510570419)
            ·
              refine ⟨4437561788833031265855629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958374525888687510570419 4437561788833031265855629)
              ·
                refine ⟨1664085670812386724695861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4437561788833031265855629 1664085670812386724695861)
                ·
                  refine ⟨156008031638661255440237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1664085670812386724695861 156008031638661255440237)
                  ·
                    rfl

theorem cell23_2734421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_2734421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734421 prefixEnd_2734421 := by exact prefixLift 2734421
  have htrace : WordTrace (prefixWord ++ tailWord_2734421) baseStart_2734421 baseEnd_2734421 := by
    simpa [prefixWord, tailWord_2734421, baseEnd_2734421] using wordTrace_append hprefix tailTrace_2734421
  have hstable : (prefixWord ++ tailWord_2734421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734421).length < 2 ^ (prefixWord ++ tailWord_2734421).sum := by decide
  have hdescent : baseEnd_2734421 < baseStart_2734421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734434 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2734434 : Nat := 118140960795 + 2734434 * 2 ^ 59
def prefixEnd_2734434 : Nat := 4983230072969 + 3 ^ 40 * 2734434 * 2
def baseEnd_2734434 : Nat := 468026319998819916033191

theorem tailTrace_2734434 : CollatzResearch.WordTrace tailWord_2734434 prefixEnd_2734434 468026319998819916033191 := by
  unfold tailWord_2734434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24933250343905024248052589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66488667583746731328140237 24933250343905024248052589)
  ·
    refine ⟨9349968878964384093019721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24933250343905024248052589 9349968878964384093019721)
    ·
      refine ⟨7012476659223288069764791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9349968878964384093019721 7012476659223288069764791)
      ·
        refine ⟨10518714988834932104647187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7012476659223288069764791 10518714988834932104647187)
        ·
          refine ⟨15778072483252398156970781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10518714988834932104647187 15778072483252398156970781)
          ·
            refine ⟨5916777181219649308864043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15778072483252398156970781 5916777181219649308864043)
            ·
              refine ⟨8875165771829473963296065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5916777181219649308864043 8875165771829473963296065)
              ·
                refine ⟨6656374328872105472472049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8875165771829473963296065 6656374328872105472472049)
                ·
                  refine ⟨4992280746654079104354037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6656374328872105472472049 4992280746654079104354037)
                  ·
                    refine ⟨468026319998819916033191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4992280746654079104354037 468026319998819916033191)
                    ·
                      rfl

theorem cell23_2734434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2734434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734434 prefixEnd_2734434 := by exact prefixLift 2734434
  have htrace : WordTrace (prefixWord ++ tailWord_2734434) baseStart_2734434 baseEnd_2734434 := by
    simpa [prefixWord, tailWord_2734434, baseEnd_2734434] using wordTrace_append hprefix tailTrace_2734434
  have hstable : (prefixWord ++ tailWord_2734434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734434).length < 2 ^ (prefixWord ++ tailWord_2734434).sum := by decide
  have hdescent : baseEnd_2734434 < baseStart_2734434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734437 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_2734437 : Nat := 118140960795 + 2734437 * 2 ^ 59
def prefixEnd_2734437 : Nat := 4983230072969 + 3 ^ 40 * 2734437 * 2
def baseEnd_2734437 : Nat := 1404080500438423236362059

theorem tailTrace_2734437 : CollatzResearch.WordTrace tailWord_2734437 prefixEnd_2734437 1404080500438423236362059 := by
  unfold tailWord_2734437
  simp only [CollatzResearch.WordTrace]
  refine ⟨99733110794609228504569565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66488740529739485669713043 99733110794609228504569565)
  ·
    refine ⟨37399916547978460689213587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99733110794609228504569565 37399916547978460689213587)
    ·
      refine ⟨56099874821967691033820381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37399916547978460689213587 56099874821967691033820381)
      ·
        refine ⟨21037453058237884137682643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56099874821967691033820381 21037453058237884137682643)
        ·
          refine ⟨31556179587356826206523965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21037453058237884137682643 31556179587356826206523965)
          ·
            refine ⟨11833567345258809827446487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31556179587356826206523965 11833567345258809827446487)
            ·
              refine ⟨17750351017888214741169731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11833567345258809827446487 17750351017888214741169731)
              ·
                refine ⟨26625526526832322111754597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17750351017888214741169731 26625526526832322111754597)
                ·
                  refine ⟨4992286223781060395953987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26625526526832322111754597 4992286223781060395953987)
                  ·
                    refine ⟨7488429335671590593930981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4992286223781060395953987 7488429335671590593930981)
                    ·
                      refine ⟨1404080500438423236362059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7488429335671590593930981 1404080500438423236362059)
                      ·
                        rfl

theorem cell23_2734437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_2734437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734437 prefixEnd_2734437 := by exact prefixLift 2734437
  have htrace : WordTrace (prefixWord ++ tailWord_2734437) baseStart_2734437 baseEnd_2734437 := by
    simpa [prefixWord, tailWord_2734437, baseEnd_2734437] using wordTrace_append hprefix tailTrace_2734437
  have hstable : (prefixWord ++ tailWord_2734437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734437).length < 2 ^ (prefixWord ++ tailWord_2734437).sum := by decide
  have hdescent : baseEnd_2734437 < baseStart_2734437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734447 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 3, 4]
def baseStart_2734447 : Nat := 118140960795 + 2734447 * 2 ^ 59
def prefixEnd_2734447 : Nat := 4983230072969 + 3 ^ 40 * 2734447 * 2
def baseEnd_2734447 : Nat := 468028545081656065745671

theorem tailTrace_2734447 : CollatzResearch.WordTrace tailWord_2734447 prefixEnd_2734447 468028545081656065745671 := by
  unfold tailWord_2734447
  simp only [CollatzResearch.WordTrace]
  refine ⟨99733475524573000212433595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66488983683048666808289063 99733475524573000212433595)
  ·
    refine ⟨149600213286859500318650393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99733475524573000212433595 149600213286859500318650393)
    ·
      refine ⟨112200159965144625238987795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149600213286859500318650393 112200159965144625238987795)
      ·
        refine ⟨168300239947716937858481693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112200159965144625238987795 168300239947716937858481693)
        ·
          refine ⟨63112589980393851696930635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168300239947716937858481693 63112589980393851696930635)
          ·
            refine ⟨94668884970590777545395953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63112589980393851696930635 94668884970590777545395953)
            ·
              refine ⟨71001663727943083159046965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94668884970590777545395953 71001663727943083159046965)
              ·
                refine ⟨6656405974494664046160653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71001663727943083159046965 6656405974494664046160653)
                ·
                  refine ⟨2496152240435499017310245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6656405974494664046160653 2496152240435499017310245)
                  ·
                    refine ⟨468028545081656065745671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496152240435499017310245 468028545081656065745671)
                    ·
                      rfl

theorem cell23_2734447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 4].length) (baseStart_2734447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734447 prefixEnd_2734447 := by exact prefixLift 2734447
  have htrace : WordTrace (prefixWord ++ tailWord_2734447) baseStart_2734447 baseEnd_2734447 := by
    simpa [prefixWord, tailWord_2734447, baseEnd_2734447] using wordTrace_append hprefix tailTrace_2734447
  have hstable : (prefixWord ++ tailWord_2734447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734447).length < 2 ^ (prefixWord ++ tailWord_2734447).sum := by decide
  have hdescent : baseEnd_2734447 < baseStart_2734447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734457 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 3]
def baseStart_2734457 : Nat := 118140960795 + 2734457 * 2 ^ 59
def prefixEnd_2734457 : Nat := 4983230072969 + 3 ^ 40 * 2734457 * 2
def baseEnd_2734457 : Nat := 1404090770051513158111967

theorem tailTrace_2734457 : CollatzResearch.WordTrace tailWord_2734457 prefixEnd_2734457 1404090770051513158111967 := by
  unfold tailWord_2734457
  simp only [CollatzResearch.WordTrace]
  refine ⟨99733840254536771920297625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66489226836357847946865083 99733840254536771920297625)
  ·
    refine ⟨74800380190902578940223219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99733840254536771920297625 74800380190902578940223219)
    ·
      refine ⟨112200570286353868410334829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74800380190902578940223219 112200570286353868410334829)
      ·
        refine ⟨42075213857382700653875561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112200570286353868410334829 42075213857382700653875561)
        ·
          refine ⟨31556410393037025490406671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42075213857382700653875561 31556410393037025490406671)
          ·
            refine ⟨47334615589555538235610007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31556410393037025490406671 47334615589555538235610007)
            ·
              refine ⟨71001923384333307353415011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47334615589555538235610007 71001923384333307353415011)
              ·
                refine ⟨106502885076499961030122517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71001923384333307353415011 106502885076499961030122517)
                ·
                  refine ⟨4992322737960935673286993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106502885076499961030122517 4992322737960935673286993)
                  ·
                    refine ⟨3744242053470701754965245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4992322737960935673286993 3744242053470701754965245)
                    ·
                      refine ⟨1404090770051513158111967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3744242053470701754965245 1404090770051513158111967)
                      ·
                        rfl

theorem cell23_2734457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2734457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734457 prefixEnd_2734457 := by exact prefixLift 2734457
  have htrace : WordTrace (prefixWord ++ tailWord_2734457) baseStart_2734457 baseEnd_2734457 := by
    simpa [prefixWord, tailWord_2734457, baseEnd_2734457] using wordTrace_append hprefix tailTrace_2734457
  have hstable : (prefixWord ++ tailWord_2734457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734457).length < 2 ^ (prefixWord ++ tailWord_2734457).sum := by decide
  have hdescent : baseEnd_2734457 < baseStart_2734457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734460 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 10]
def baseStart_2734460 : Nat := 118140960795 + 2734460 * 2 ^ 59
def prefixEnd_2734460 : Nat := 4983230072969 + 3 ^ 40 * 2734460 * 2
def baseEnd_2734460 : Nat := 156010256721497405152717

theorem tailTrace_2734460 : CollatzResearch.WordTrace tailWord_2734460 prefixEnd_2734460 156010256721497405152717 := by
  unfold tailWord_2734460
  simp only [CollatzResearch.WordTrace]
  refine ⟨49866974836762951716328417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66489299782350602288437889 49866974836762951716328417)
  ·
    refine ⟨37400231127572213787246313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49866974836762951716328417 37400231127572213787246313)
    ·
      refine ⟨28050173345679160340434735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37400231127572213787246313 28050173345679160340434735)
      ·
        refine ⟨42075260018518740510652103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28050173345679160340434735 42075260018518740510652103)
        ·
          refine ⟨63112890027778110765978155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42075260018518740510652103 63112890027778110765978155)
          ·
            refine ⟨94669335041667166148967233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63112890027778110765978155 94669335041667166148967233)
            ·
              refine ⟨71002001281250374611725425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94669335041667166148967233 71002001281250374611725425)
              ·
                refine ⟨53251500960937780958794069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71002001281250374611725425 53251500960937780958794069)
                ·
                  refine ⟨156010256721497405152717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 53251500960937780958794069 156010256721497405152717)
                  ·
                    rfl

theorem cell23_2734460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_2734460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734460 prefixEnd_2734460 := by exact prefixLift 2734460
  have htrace : WordTrace (prefixWord ++ tailWord_2734460) baseStart_2734460 baseEnd_2734460 := by
    simpa [prefixWord, tailWord_2734460, baseEnd_2734460] using wordTrace_append hprefix tailTrace_2734460
  have hstable : (prefixWord ++ tailWord_2734460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734460).length < 2 ^ (prefixWord ++ tailWord_2734460).sum := by decide
  have hdescent : baseEnd_2734460 < baseStart_2734460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734480 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_2734480 : Nat := 118140960795 + 2734480 * 2 ^ 59
def prefixEnd_2734480 : Nat := 4983230072969 + 3 ^ 40 * 2734480 * 2
def baseEnd_2734480 : Nat := 1404102580106566568124361

theorem tailTrace_2734480 : CollatzResearch.WordTrace tailWord_2734480 prefixEnd_2734480 1404102580106566568124361 := by
  unfold tailWord_2734480
  simp only [CollatzResearch.WordTrace]
  refine ⟨49867339566726723424192447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66489786088968964565589929 49867339566726723424192447)
  ·
    refine ⟨74801009350090085136288671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49867339566726723424192447 74801009350090085136288671)
    ·
      refine ⟨112201514025135127704433007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74801009350090085136288671 112201514025135127704433007)
      ·
        refine ⟨168302271037702691556649511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112201514025135127704433007 168302271037702691556649511)
        ·
          refine ⟨252453406556554037334974267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168302271037702691556649511 252453406556554037334974267)
          ·
            refine ⟨378680109834831056002461401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252453406556554037334974267 378680109834831056002461401)
            ·
              refine ⟨284010082376123292001846051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378680109834831056002461401 284010082376123292001846051)
              ·
                refine ⟨426015123564184938002769077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284010082376123292001846051 426015123564184938002769077)
                ·
                  refine ⟨39938917834142337937759601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 426015123564184938002769077 39938917834142337937759601)
                  ·
                    refine ⟨29954188375606753453319701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39938917834142337937759601 29954188375606753453319701)
                    ·
                      refine ⟨1404102580106566568124361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29954188375606753453319701 1404102580106566568124361)
                      ·
                        rfl

theorem cell23_2734480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_2734480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734480 prefixEnd_2734480 := by exact prefixLift 2734480
  have htrace : WordTrace (prefixWord ++ tailWord_2734480) baseStart_2734480 baseEnd_2734480 := by
    simpa [prefixWord, tailWord_2734480, baseEnd_2734480] using wordTrace_append hprefix tailTrace_2734480
  have hstable : (prefixWord ++ tailWord_2734480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734480).length < 2 ^ (prefixWord ++ tailWord_2734480).sum := by decide
  have hdescent : baseEnd_2734480 < baseStart_2734480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734514 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_2734514 : Nat := 118140960795 + 2734514 * 2 ^ 59
def prefixEnd_2734514 : Nat := 4983230072969 + 3 ^ 40 * 2734514 * 2
def baseEnd_2734514 : Nat := 1404120038448819435099205

theorem tailTrace_2734514 : CollatzResearch.WordTrace tailWord_2734514 prefixEnd_2734514 1404120038448819435099205 := by
  unfold tailWord_2734514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24933979803832567663780649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66490612810220180436748397 24933979803832567663780649)
  ·
    refine ⟨18700484852874425747835487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24933979803832567663780649 18700484852874425747835487)
    ·
      refine ⟨28050727279311638621753231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18700484852874425747835487 28050727279311638621753231)
      ·
        refine ⟨42076090918967457932629847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28050727279311638621753231 42076090918967457932629847)
        ·
          refine ⟨63114136378451186898944771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42076090918967457932629847 63114136378451186898944771)
          ·
            refine ⟨94671204567676780348417157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63114136378451186898944771 94671204567676780348417157)
            ·
              refine ⟨17750850856439396315328217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94671204567676780348417157 17750850856439396315328217)
              ·
                refine ⟨13313138142329547236496163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17750850856439396315328217 13313138142329547236496163)
                ·
                  refine ⟨19969707213494320854744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13313138142329547236496163 19969707213494320854744245)
                  ·
                    refine ⟨1872160051265092580132273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19969707213494320854744245 1872160051265092580132273)
                    ·
                      refine ⟨1404120038448819435099205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872160051265092580132273 1404120038448819435099205)
                      ·
                        rfl

theorem cell23_2734514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_2734514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734514 prefixEnd_2734514 := by exact prefixLift 2734514
  have htrace : WordTrace (prefixWord ++ tailWord_2734514) baseStart_2734514 baseEnd_2734514 := by
    simpa [prefixWord, tailWord_2734514, baseEnd_2734514] using wordTrace_append hprefix tailTrace_2734514
  have hstable : (prefixWord ++ tailWord_2734514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734514).length < 2 ^ (prefixWord ++ tailWord_2734514).sum := by decide
  have hdescent : baseEnd_2734514 < baseStart_2734514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734521 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2734521 : Nat := 118140960795 + 2734521 * 2 ^ 59
def prefixEnd_2734521 : Nat := 4983230072969 + 3 ^ 40 * 2734521 * 2
def baseEnd_2734521 : Nat := 1404123632813400907711673

theorem tailTrace_2734521 : CollatzResearch.WordTrace tailWord_2734521 prefixEnd_2734521 1404123632813400907711673 := by
  unfold tailWord_2734521
  simp only [CollatzResearch.WordTrace]
  refine ⟨99736174526304910850627417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66490783017536607233751611 99736174526304910850627417)
  ·
    refine ⟨74802130894728683137970563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99736174526304910850627417 74802130894728683137970563)
    ·
      refine ⟨112203196342093024706955845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74802130894728683137970563 112203196342093024706955845)
      ·
        refine ⟨21038099314142442132554221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112203196342093024706955845 21038099314142442132554221)
        ·
          refine ⟨7889287242803415799707833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21038099314142442132554221 7889287242803415799707833)
          ·
            refine ⟨5916965432102561849780875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7889287242803415799707833 5916965432102561849780875)
            ·
              refine ⟨8875448148153842774671313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5916965432102561849780875 8875448148153842774671313)
              ·
                refine ⟨6656586111115382081003485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8875448148153842774671313 6656586111115382081003485)
                ·
                  refine ⟨2496219791668268280376307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6656586111115382081003485 2496219791668268280376307)
                  ·
                    refine ⟨3744329687502402420564461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2496219791668268280376307 3744329687502402420564461)
                    ·
                      refine ⟨1404123632813400907711673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3744329687502402420564461 1404123632813400907711673)
                      ·
                        rfl

theorem cell23_2734521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2734521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734521 prefixEnd_2734521 := by exact prefixLift 2734521
  have htrace : WordTrace (prefixWord ++ tailWord_2734521) baseStart_2734521 baseEnd_2734521 := by
    simpa [prefixWord, tailWord_2734521, baseEnd_2734521] using wordTrace_append hprefix tailTrace_2734521
  have hstable : (prefixWord ++ tailWord_2734521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734521).length < 2 ^ (prefixWord ++ tailWord_2734521).sum := by decide
  have hdescent : baseEnd_2734521 < baseStart_2734521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734524 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_2734524 : Nat := 118140960795 + 2734524 * 2 ^ 59
def prefixEnd_2734524 : Nat := 4983230072969 + 3 ^ 40 * 2734524 * 2
def baseEnd_2734524 : Nat := 468041724418454798658053

theorem tailTrace_2734524 : CollatzResearch.WordTrace tailWord_2734524 prefixEnd_2734524 468041724418454798658053 := by
  unfold tailWord_2734524
  simp only [CollatzResearch.WordTrace]
  refine ⟨49868141972647021181493313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66490855963529361575324417 49868141972647021181493313)
  ·
    refine ⟨37401106479485265886119985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49868141972647021181493313 37401106479485265886119985)
    ·
      refine ⟨28050829859613949414589989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37401106479485265886119985 28050829859613949414589989)
      ·
        refine ⟨5259530598677615515235623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28050829859613949414589989 5259530598677615515235623)
        ·
          refine ⟨7889295898016423272853435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259530598677615515235623 7889295898016423272853435)
          ·
            refine ⟨11833943847024634909280153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7889295898016423272853435 11833943847024634909280153)
            ·
              refine ⟨8875457885268476181960115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11833943847024634909280153 8875457885268476181960115)
              ·
                refine ⟨13313186827902714272940173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8875457885268476181960115 13313186827902714272940173)
                ·
                  refine ⟨4992445060463517852352565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13313186827902714272940173 4992445060463517852352565)
                  ·
                    refine ⟨468041724418454798658053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4992445060463517852352565 468041724418454798658053)
                    ·
                      rfl

theorem cell23_2734524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_2734524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734524 prefixEnd_2734524 := by exact prefixLift 2734524
  have htrace : WordTrace (prefixWord ++ tailWord_2734524) baseStart_2734524 baseEnd_2734524 := by
    simpa [prefixWord, tailWord_2734524, baseEnd_2734524] using wordTrace_append hprefix tailTrace_2734524
  have hstable : (prefixWord ++ tailWord_2734524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734524).length < 2 ^ (prefixWord ++ tailWord_2734524).sum := by decide
  have hdescent : baseEnd_2734524 < baseStart_2734524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734537 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 1, 6]
def baseStart_2734537 : Nat := 118140960795 + 2734537 * 2 ^ 59
def prefixEnd_2734537 : Nat := 4983230072969 + 3 ^ 40 * 2734537 * 2
def baseEnd_2734537 : Nat := 468043949501290948370533

theorem tailTrace_2734537 : CollatzResearch.WordTrace tailWord_2734537 prefixEnd_2734537 468043949501290948370533 := by
  unfold tailWord_2734537
  simp only [CollatzResearch.WordTrace]
  refine ⟨99736758094246945583209865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66491172062831297055473243 99736758094246945583209865)
  ·
    refine ⟨74802568570685209187407399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99736758094246945583209865 74802568570685209187407399)
    ·
      refine ⟨112203852856027813781111099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74802568570685209187407399 112203852856027813781111099)
      ·
        refine ⟨168305779284041720671666649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112203852856027813781111099 168305779284041720671666649)
        ·
          refine ⟨126229334463031290503749987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168305779284041720671666649 126229334463031290503749987)
          ·
            refine ⟨189344001694546935755624981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126229334463031290503749987 189344001694546935755624981)
            ·
              refine ⟨8875500079431887613544921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189344001694546935755624981 8875500079431887613544921)
              ·
                refine ⟨6656625059573915710158691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8875500079431887613544921 6656625059573915710158691)
                ·
                  refine ⟨9984937589360873565238037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6656625059573915710158691 9984937589360873565238037)
                  ·
                    refine ⟨468043949501290948370533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9984937589360873565238037 468043949501290948370533)
                    ·
                      rfl

theorem cell23_2734537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_2734537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734537 prefixEnd_2734537 := by exact prefixLift 2734537
  have htrace : WordTrace (prefixWord ++ tailWord_2734537) baseStart_2734537 baseEnd_2734537 := by
    simpa [prefixWord, tailWord_2734537, baseEnd_2734537] using wordTrace_append hprefix tailTrace_2734537
  have hstable : (prefixWord ++ tailWord_2734537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734537).length < 2 ^ (prefixWord ++ tailWord_2734537).sum := by decide
  have hdescent : baseEnd_2734537 < baseStart_2734537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734538 : List Nat := [3, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3]
def baseStart_2734538 : Nat := 118140960795 + 2734538 * 2 ^ 59
def prefixEnd_2734538 : Nat := 4983230072969 + 3 ^ 40 * 2734538 * 2
def baseEnd_2734538 : Nat := 1404132361984527341199095

theorem tailTrace_2734538 : CollatzResearch.WordTrace tailWord_2734538 prefixEnd_2734538 1404132361984527341199095 := by
  unfold tailWord_2734538
  simp only [CollatzResearch.WordTrace]
  refine ⟨24934198641810830688499067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66491196378162215169330845 24934198641810830688499067)
  ·
    refine ⟨37401297962716246032748601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24934198641810830688499067 37401297962716246032748601)
    ·
      refine ⟨28050973472037184524561451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37401297962716246032748601 28050973472037184524561451)
      ·
        refine ⟨42076460208055776786842177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28050973472037184524561451 42076460208055776786842177)
        ·
          refine ⟨31557345156041832590131633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42076460208055776786842177 31557345156041832590131633)
          ·
            refine ⟨23668008867031374442598725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31557345156041832590131633 23668008867031374442598725)
            ·
              refine ⟨4437751662568382707987261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23668008867031374442598725 4437751662568382707987261)
              ·
                refine ⟨1664156873463143515495223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4437751662568382707987261 1664156873463143515495223)
                ·
                  refine ⟨2496235310194715273242835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664156873463143515495223 2496235310194715273242835)
                  ·
                    refine ⟨3744352965292072909864253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2496235310194715273242835 3744352965292072909864253)
                    ·
                      refine ⟨1404132361984527341199095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3744352965292072909864253 1404132361984527341199095)
                      ·
                        rfl

theorem cell23_2734538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_2734538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734538 prefixEnd_2734538 := by exact prefixLift 2734538
  have htrace : WordTrace (prefixWord ++ tailWord_2734538) baseStart_2734538 baseEnd_2734538 := by
    simpa [prefixWord, tailWord_2734538, baseEnd_2734538] using wordTrace_append hprefix tailTrace_2734538
  have hstable : (prefixWord ++ tailWord_2734538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734538).length < 2 ^ (prefixWord ++ tailWord_2734538).sum := by decide
  have hdescent : baseEnd_2734538 < baseStart_2734538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734554 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_2734554 : Nat := 118140960795 + 2734554 * 2 ^ 59
def prefixEnd_2734554 : Nat := 4983230072969 + 3 ^ 40 * 2734554 * 2
def baseEnd_2734554 : Nat := 468046859224999759533007

theorem tailTrace_2734554 : CollatzResearch.WordTrace tailWord_2734554 prefixEnd_2734554 468046859224999759533007 := by
  unfold tailWord_2734554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24934344533796339371644679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66491585423456904991052477 24934344533796339371644679)
  ·
    refine ⟨37401516800694509057467019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24934344533796339371644679 37401516800694509057467019)
    ·
      refine ⟨56102275201041763586200529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37401516800694509057467019 56102275201041763586200529)
      ·
        refine ⟨42076706400781322689650397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56102275201041763586200529 42076706400781322689650397)
        ·
          refine ⟨15778764900292996008618899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42076706400781322689650397 15778764900292996008618899)
          ·
            refine ⟨23668147350439494012928349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15778764900292996008618899 23668147350439494012928349)
            ·
              refine ⟨8875555256414810254848131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23668147350439494012928349 8875555256414810254848131)
              ·
                refine ⟨13313332884622215382272197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8875555256414810254848131 13313332884622215382272197)
                ·
                  refine ⟨2496249915866665384176037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13313332884622215382272197 2496249915866665384176037)
                  ·
                    refine ⟨468046859224999759533007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496249915866665384176037 468046859224999759533007)
                    ·
                      rfl

theorem cell23_2734554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_2734554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734554 prefixEnd_2734554 := by exact prefixLift 2734554
  have htrace : WordTrace (prefixWord ++ tailWord_2734554) baseStart_2734554 baseEnd_2734554 := by
    simpa [prefixWord, tailWord_2734554, baseEnd_2734554] using wordTrace_append hprefix tailTrace_2734554
  have hstable : (prefixWord ++ tailWord_2734554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734554).length < 2 ^ (prefixWord ++ tailWord_2734554).sum := by decide
  have hdescent : baseEnd_2734554 < baseStart_2734554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734567 : List Nat := [1, 1, 5, 2, 1, 1, 2, 10]
def baseStart_2734567 : Nat := 118140960795 + 2734567 * 2 ^ 59
def prefixEnd_2734567 : Nat := 4983230072969 + 3 ^ 40 * 2734567 * 2
def baseEnd_2734567 : Nat := 52005453811981767693943

theorem tailTrace_2734567 : CollatzResearch.WordTrace tailWord_2734567 prefixEnd_2734567 52005453811981767693943 := by
  unfold tailWord_2734567
  simp only [CollatzResearch.WordTrace]
  refine ⟨99737852284138260706801955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66491901522758840471201303 99737852284138260706801955)
  ·
    refine ⟨149606778426207391060202933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99737852284138260706801955 149606778426207391060202933)
    ·
      refine ⟨14025635477456942911894025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149606778426207391060202933 14025635477456942911894025)
      ·
        refine ⟨10519226608092707183920519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14025635477456942911894025 10519226608092707183920519)
        ·
          refine ⟨15778839912139060775880779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10519226608092707183920519 15778839912139060775880779)
          ·
            refine ⟨23668259868208591163821169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15778839912139060775880779 23668259868208591163821169)
            ·
              refine ⟨17751194901156443372865877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23668259868208591163821169 17751194901156443372865877)
              ·
                refine ⟨52005453811981767693943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17751194901156443372865877 52005453811981767693943)
                ·
                  rfl

theorem cell23_2734567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 10].length) (baseStart_2734567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734567 prefixEnd_2734567 := by exact prefixLift 2734567
  have htrace : WordTrace (prefixWord ++ tailWord_2734567) baseStart_2734567 baseEnd_2734567 := by
    simpa [prefixWord, tailWord_2734567, baseEnd_2734567] using wordTrace_append hprefix tailTrace_2734567
  have hstable : (prefixWord ++ tailWord_2734567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734567).length < 2 ^ (prefixWord ++ tailWord_2734567).sum := by decide
  have hdescent : baseEnd_2734567 < baseStart_2734567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734571 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 2, 4]
def baseStart_2734571 : Nat := 118140960795 + 2734571 * 2 ^ 59
def prefixEnd_2734571 : Nat := 4983230072969 + 3 ^ 40 * 2734571 * 2
def baseEnd_2734571 : Nat := 468049768948708570695481

theorem tailTrace_2734571 : CollatzResearch.WordTrace tailWord_2734571 prefixEnd_2734571 468049768948708570695481 := by
  unfold tailWord_2734571
  simp only [CollatzResearch.WordTrace]
  refine ⟨99737998176123769389947567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66491998784082512926631711 99737998176123769389947567)
  ·
    refine ⟨149606997264185654084921351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99737998176123769389947567 149606997264185654084921351)
    ·
      refine ⟨224410495896278481127382027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149606997264185654084921351 224410495896278481127382027)
      ·
        refine ⟨336615743844417721691073041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224410495896278481127382027 336615743844417721691073041)
        ·
          refine ⟨252461807883313291268304781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336615743844417721691073041 252461807883313291268304781)
          ·
            refine ⟨94673177956242484225614293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252461807883313291268304781 94673177956242484225614293)
            ·
              refine ⟨2218902608349433224037835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94673177956242484225614293 2218902608349433224037835)
              ·
                refine ⟨3328353912524149836056753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2218902608349433224037835 3328353912524149836056753)
                ·
                  refine ⟨2496265434393112377042565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3328353912524149836056753 2496265434393112377042565)
                  ·
                    refine ⟨468049768948708570695481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496265434393112377042565 468049768948708570695481)
                    ·
                      rfl

theorem cell23_2734571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 4].length) (baseStart_2734571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734571 prefixEnd_2734571 := by exact prefixLift 2734571
  have htrace : WordTrace (prefixWord ++ tailWord_2734571) baseStart_2734571 baseEnd_2734571 := by
    simpa [prefixWord, tailWord_2734571, baseEnd_2734571] using wordTrace_append hprefix tailTrace_2734571
  have hstable : (prefixWord ++ tailWord_2734571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734571).length < 2 ^ (prefixWord ++ tailWord_2734571).sum := by decide
  have hdescent : baseEnd_2734571 < baseStart_2734571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734574 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2734574 : Nat := 118140960795 + 2734574 * 2 ^ 59
def prefixEnd_2734574 : Nat := 4983230072969 + 3 ^ 40 * 2734574 * 2
def baseEnd_2734574 : Nat := 1404150847288089200348929

theorem tailTrace_2734574 : CollatzResearch.WordTrace tailWord_2734574 prefixEnd_2734574 1404150847288089200348929 := by
  unfold tailWord_2734574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12467263449389112612788347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66492071730075267268204517 12467263449389112612788347)
  ·
    refine ⟨18700895174083668919182521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12467263449389112612788347 18700895174083668919182521)
    ·
      refine ⟨14025671380562751689386891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18700895174083668919182521 14025671380562751689386891)
      ·
        refine ⟨21038507070844127534080337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14025671380562751689386891 21038507070844127534080337)
        ·
          refine ⟨15778880303133095650560253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21038507070844127534080337 15778880303133095650560253)
          ·
            refine ⟨5917080113674910868960095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15778880303133095650560253 5917080113674910868960095)
            ·
              refine ⟨8875620170512366303440143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5917080113674910868960095 8875620170512366303440143)
              ·
                refine ⟨13313430255768549455160215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8875620170512366303440143 13313430255768549455160215)
                ·
                  refine ⟨19970145383652824182740323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13313430255768549455160215 19970145383652824182740323)
                  ·
                    refine ⟨29955218075479236274110485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19970145383652824182740323 29955218075479236274110485)
                    ·
                      refine ⟨1404150847288089200348929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29955218075479236274110485 1404150847288089200348929)
                      ·
                        rfl

theorem cell23_2734574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2734574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734574 prefixEnd_2734574 := by exact prefixLift 2734574
  have htrace : WordTrace (prefixWord ++ tailWord_2734574) baseStart_2734574 baseEnd_2734574 := by
    simpa [prefixWord, tailWord_2734574, baseEnd_2734574] using wordTrace_append hprefix tailTrace_2734574
  have hstable : (prefixWord ++ tailWord_2734574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734574).length < 2 ^ (prefixWord ++ tailWord_2734574).sum := by decide
  have hdescent : baseEnd_2734574 < baseStart_2734574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734578 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2734578 : Nat := 118140960795 + 2734578 * 2 ^ 59
def prefixEnd_2734578 : Nat := 4983230072969 + 3 ^ 40 * 2734578 * 2
def baseEnd_2734578 : Nat := 1404152901210707184698911

theorem tailTrace_2734578 : CollatzResearch.WordTrace tailWord_2734578 prefixEnd_2734578 1404152901210707184698911 := by
  unfold tailWord_2734578
  simp only [CollatzResearch.WordTrace]
  refine ⟨24934563371774602396363097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66492168991398939723634925 24934563371774602396363097)
  ·
    refine ⟨18700922528830951797272323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24934563371774602396363097 18700922528830951797272323)
    ·
      refine ⟨28051383793246427695908485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18700922528830951797272323 28051383793246427695908485)
      ·
        refine ⟨5259634461233705192982841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28051383793246427695908485 5259634461233705192982841)
        ·
          refine ⟨3944725845925278894737131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5259634461233705192982841 3944725845925278894737131)
          ·
            refine ⟨5917088768887918342105697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3944725845925278894737131 5917088768887918342105697)
            ·
              refine ⟨4437816576665938756579273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5917088768887918342105697 4437816576665938756579273)
              ·
                refine ⟨3328362432499454067434455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4437816576665938756579273 3328362432499454067434455)
                ·
                  refine ⟨4992543648749181101151683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3328362432499454067434455 4992543648749181101151683)
                  ·
                    refine ⟨7488815473123771651727525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4992543648749181101151683 7488815473123771651727525)
                    ·
                      refine ⟨1404152901210707184698911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7488815473123771651727525 1404152901210707184698911)
                      ·
                        rfl

theorem cell23_2734578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2734578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734578 prefixEnd_2734578 := by exact prefixLift 2734578
  have htrace : WordTrace (prefixWord ++ tailWord_2734578) baseStart_2734578 baseEnd_2734578 := by
    simpa [prefixWord, tailWord_2734578, baseEnd_2734578] using wordTrace_append hprefix tailTrace_2734578
  have hstable : (prefixWord ++ tailWord_2734578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734578).length < 2 ^ (prefixWord ++ tailWord_2734578).sum := by decide
  have hdescent : baseEnd_2734578 < baseStart_2734578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734611 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 3]
def baseStart_2734611 : Nat := 118140960795 + 2734611 * 2 ^ 59
def prefixEnd_2734611 : Nat := 4983230072969 + 3 ^ 40 * 2734611 * 2
def baseEnd_2734611 : Nat := 1404169846072305555586259

theorem tailTrace_2734611 : CollatzResearch.WordTrace tailWord_2734611 prefixEnd_2734611 1404169846072305555586259 := by
  unfold tailWord_2734611
  simp only [CollatzResearch.WordTrace]
  refine ⟨99739457095978856221403687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66492971397319237480935791 99739457095978856221403687)
  ·
    refine ⟨149609185643968284332105531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99739457095978856221403687 149609185643968284332105531)
    ·
      refine ⟨224413778465952426498158297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149609185643968284332105531 224413778465952426498158297)
      ·
        refine ⟨168310333849464319873618723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224413778465952426498158297 168310333849464319873618723)
        ·
          refine ⟨252465500774196479810428085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168310333849464319873618723 252465500774196479810428085)
          ·
            refine ⟨23668640697580919982227633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252465500774196479810428085 23668640697580919982227633)
            ·
              refine ⟨17751480523185689986670725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23668640697580919982227633 17751480523185689986670725)
              ·
                refine ⟨3328402598097316872500761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17751480523185689986670725 3328402598097316872500761)
                ·
                  refine ⟨2496301948572987654375571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3328402598097316872500761 2496301948572987654375571)
                  ·
                    refine ⟨3744452922859481481563357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2496301948572987654375571 3744452922859481481563357)
                    ·
                      refine ⟨1404169846072305555586259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3744452922859481481563357 1404169846072305555586259)
                      ·
                        rfl

theorem cell23_2734611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 3].length) (baseStart_2734611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734611 prefixEnd_2734611 := by exact prefixLift 2734611
  have htrace : WordTrace (prefixWord ++ tailWord_2734611) baseStart_2734611 baseEnd_2734611 := by
    simpa [prefixWord, tailWord_2734611, baseEnd_2734611] using wordTrace_append hprefix tailTrace_2734611
  have hstable : (prefixWord ++ tailWord_2734611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734611).length < 2 ^ (prefixWord ++ tailWord_2734611).sum := by decide
  have hdescent : baseEnd_2734611 < baseStart_2734611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734612 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_2734612 : Nat := 118140960795 + 2734612 * 2 ^ 59
def prefixEnd_2734612 : Nat := 4983230072969 + 3 ^ 40 * 2734612 * 2
def baseEnd_2734612 : Nat := 1404170359552960051673755

theorem tailTrace_2734612 : CollatzResearch.WordTrace tailWord_2734612 prefixEnd_2734612 1404170359552960051673755 := by
  unfold tailWord_2734612
  simp only [CollatzResearch.WordTrace]
  refine ⟨49869746784487616696095045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66492995712650155594793393 49869746784487616696095045)
  ·
    refine ⟨9350577522091428130517821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49869746784487616696095045 9350577522091428130517821)
    ·
      refine ⟨3506466570784285548944183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9350577522091428130517821 3506466570784285548944183)
      ·
        refine ⟨5259699856176428323416275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3506466570784285548944183 5259699856176428323416275)
        ·
          refine ⟨7889549784264642485124413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259699856176428323416275 7889549784264642485124413)
          ·
            refine ⟨2958581169099240931921655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7889549784264642485124413 2958581169099240931921655)
            ·
              refine ⟨4437871753648861397882483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958581169099240931921655 4437871753648861397882483)
              ·
                refine ⟨6656807630473292096823725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437871753648861397882483 6656807630473292096823725)
                ·
                  refine ⟨2496302861427484536308897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6656807630473292096823725 2496302861427484536308897)
                  ·
                    refine ⟨1872227146070613402231673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2496302861427484536308897 1872227146070613402231673)
                    ·
                      refine ⟨1404170359552960051673755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872227146070613402231673 1404170359552960051673755)
                      ·
                        rfl

theorem cell23_2734612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_2734612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734612 prefixEnd_2734612 := by exact prefixLift 2734612
  have htrace : WordTrace (prefixWord ++ tailWord_2734612) baseStart_2734612 baseEnd_2734612 := by
    simpa [prefixWord, tailWord_2734612, baseEnd_2734612] using wordTrace_append hprefix tailTrace_2734612
  have hstable : (prefixWord ++ tailWord_2734612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734612).length < 2 ^ (prefixWord ++ tailWord_2734612).sum := by decide
  have hdescent : baseEnd_2734612 < baseStart_2734612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734617 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_2734617 : Nat := 118140960795 + 2734617 * 2 ^ 59
def prefixEnd_2734617 : Nat := 4983230072969 + 3 ^ 40 * 2734617 * 2
def baseEnd_2734617 : Nat := 1404172926956232532111231

theorem tailTrace_2734617 : CollatzResearch.WordTrace tailWord_2734617 prefixEnd_2734617 1404172926956232532111231 := by
  unfold tailWord_2734617
  simp only [CollatzResearch.WordTrace]
  refine ⟨99739675933957119246122105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66493117289304746164081403 99739675933957119246122105)
  ·
    refine ⟨74804756950467839434591579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99739675933957119246122105 74804756950467839434591579)
    ·
      refine ⟨112207135425701759151887369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74804756950467839434591579 112207135425701759151887369)
      ·
        refine ⟨84155351569276319363915527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112207135425701759151887369 84155351569276319363915527)
        ·
          refine ⟨126233027353914479045873291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84155351569276319363915527 126233027353914479045873291)
          ·
            refine ⟨189349541030871718568809937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126233027353914479045873291 189349541030871718568809937)
            ·
              refine ⟨142012155773153788926607453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189349541030871718568809937 142012155773153788926607453)
              ·
                refine ⟨53254558414932670847477795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142012155773153788926607453 53254558414932670847477795)
                ·
                  refine ⟨79881837622399006271216693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53254558414932670847477795 79881837622399006271216693)
                  ·
                    refine ⟨7488922277099906837926565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79881837622399006271216693 7488922277099906837926565)
                    ·
                      refine ⟨1404172926956232532111231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7488922277099906837926565 1404172926956232532111231)
                      ·
                        rfl

theorem cell23_2734617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_2734617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734617 prefixEnd_2734617 := by exact prefixLift 2734617
  have htrace : WordTrace (prefixWord ++ tailWord_2734617) baseStart_2734617 baseEnd_2734617 := by
    simpa [prefixWord, tailWord_2734617, baseEnd_2734617] using wordTrace_append hprefix tailTrace_2734617
  have hstable : (prefixWord ++ tailWord_2734617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734617).length < 2 ^ (prefixWord ++ tailWord_2734617).sum := by decide
  have hdescent : baseEnd_2734617 < baseStart_2734617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734662 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2734662 : Nat := 118140960795 + 2734662 * 2 ^ 59
def prefixEnd_2734662 : Nat := 4983230072969 + 3 ^ 40 * 2734662 * 2
def baseEnd_2734662 : Nat := 1404196033585684856048525

theorem tailTrace_2734662 : CollatzResearch.WordTrace tailWord_2734662 prefixEnd_2734662 1404196033585684856048525 := by
  unfold tailWord_2734662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116916163087315372859695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66494211479196061287673493 3116916163087315372859695)
  ·
    refine ⟨4675374244630973059289543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3116916163087315372859695 4675374244630973059289543)
    ·
      refine ⟨7013061366946459588934315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4675374244630973059289543 7013061366946459588934315)
      ·
        refine ⟨10519592050419689383401473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7013061366946459588934315 10519592050419689383401473)
        ·
          refine ⟨7889694037814767037551105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10519592050419689383401473 7889694037814767037551105)
          ·
            refine ⟨5917270528361075278163329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7889694037814767037551105 5917270528361075278163329)
            ·
              refine ⟨4437952896270806458622497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5917270528361075278163329 4437952896270806458622497)
              ·
                refine ⟨3328464672203104843966873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4437952896270806458622497 3328464672203104843966873)
                ·
                  refine ⟨2496348504152328632975155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3328464672203104843966873 2496348504152328632975155)
                  ·
                    refine ⟨3744522756228492949462733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2496348504152328632975155 3744522756228492949462733)
                    ·
                      refine ⟨1404196033585684856048525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3744522756228492949462733 1404196033585684856048525)
                      ·
                        rfl

theorem cell23_2734662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2734662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734662 prefixEnd_2734662 := by exact prefixLift 2734662
  have htrace : WordTrace (prefixWord ++ tailWord_2734662) baseStart_2734662 baseEnd_2734662 := by
    simpa [prefixWord, tailWord_2734662, baseEnd_2734662] using wordTrace_append hprefix tailTrace_2734662
  have hstable : (prefixWord ++ tailWord_2734662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734662).length < 2 ^ (prefixWord ++ tailWord_2734662).sum := by decide
  have hdescent : baseEnd_2734662 < baseStart_2734662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734667 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 7]
def baseStart_2734667 : Nat := 118140960795 + 2734667 * 2 ^ 59
def prefixEnd_2734667 : Nat := 4983230072969 + 3 ^ 40 * 2734667 * 2
def baseEnd_2734667 : Nat := 1404198600988957336486001

theorem tailTrace_2734667 : CollatzResearch.WordTrace tailWord_2734667 prefixEnd_2734667 1404198600988957336486001 := by
  unfold tailWord_2734667
  simp only [CollatzResearch.WordTrace]
  refine ⟨99741499583775977785442255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66494333055850651856961503 99741499583775977785442255)
  ·
    refine ⟨149612249375663966678163383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99741499583775977785442255 149612249375663966678163383)
    ·
      refine ⟨224418374063495950017245075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149612249375663966678163383 224418374063495950017245075)
      ·
        refine ⟨336627561095243925025867613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224418374063495950017245075 336627561095243925025867613)
        ·
          refine ⟨126235335410716471884700355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336627561095243925025867613 126235335410716471884700355)
          ·
            refine ⟨189353003116074707827050533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126235335410716471884700355 189353003116074707827050533)
            ·
              refine ⟨35503688084264007717571975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189353003116074707827050533 35503688084264007717571975)
              ·
                refine ⟨53255532126396011576357963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35503688084264007717571975 53255532126396011576357963)
                ·
                  refine ⟨79883298189594017364536945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53255532126396011576357963 79883298189594017364536945)
                  ·
                    refine ⟨59912473642195513023402709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79883298189594017364536945 59912473642195513023402709)
                    ·
                      refine ⟨1404198600988957336486001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59912473642195513023402709 1404198600988957336486001)
                      ·
                        rfl

theorem cell23_2734667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_2734667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734667 prefixEnd_2734667 := by exact prefixLift 2734667
  have htrace : WordTrace (prefixWord ++ tailWord_2734667) baseStart_2734667 baseEnd_2734667 := by
    simpa [prefixWord, tailWord_2734667, baseEnd_2734667] using wordTrace_append hprefix tailTrace_2734667
  have hstable : (prefixWord ++ tailWord_2734667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734667).length < 2 ^ (prefixWord ++ tailWord_2734667).sum := by decide
  have hdescent : baseEnd_2734667 < baseStart_2734667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734674 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 7]
def baseStart_2734674 : Nat := 118140960795 + 2734674 * 2 ^ 59
def prefixEnd_2734674 : Nat := 4983230072969 + 3 ^ 40 * 2734674 * 2
def baseEnd_2734674 : Nat := 156022466150393201010941

theorem tailTrace_2734674 : CollatzResearch.WordTrace tailWord_2734674 prefixEnd_2734674 156022466150393201010941 := by
  unfold tailWord_2734674
  simp only [CollatzResearch.WordTrace]
  refine ⟨24935438723687654495236769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66494503263167078653964717 24935438723687654495236769)
  ·
    refine ⟨18701579042765740871427577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24935438723687654495236769 18701579042765740871427577)
    ·
      refine ⟨14026184282074305653570683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18701579042765740871427577 14026184282074305653570683)
      ·
        refine ⟨21039276423111458480356025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14026184282074305653570683 21039276423111458480356025)
        ·
          refine ⟨15779457317333593860267019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21039276423111458480356025 15779457317333593860267019)
          ·
            refine ⟨23669185976000390790400529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15779457317333593860267019 23669185976000390790400529)
            ·
              refine ⟨17751889482000293092800397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23669185976000390790400529 17751889482000293092800397)
              ·
                refine ⟨6656958555750109909800149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17751889482000293092800397 6656958555750109909800149)
                ·
                  refine ⟨156022466150393201010941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6656958555750109909800149 156022466150393201010941)
                  ·
                    rfl

theorem cell23_2734674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_2734674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734674 prefixEnd_2734674 := by exact prefixLift 2734674
  have htrace : WordTrace (prefixWord ++ tailWord_2734674) baseStart_2734674 baseEnd_2734674 := by
    simpa [prefixWord, tailWord_2734674, baseEnd_2734674] using wordTrace_append hprefix tailTrace_2734674
  have hstable : (prefixWord ++ tailWord_2734674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734674).length < 2 ^ (prefixWord ++ tailWord_2734674).sum := by decide
  have hdescent : baseEnd_2734674 < baseStart_2734674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734798 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_2734798 : Nat := 118140960795 + 2734798 * 2 ^ 59
def prefixEnd_2734798 : Nat := 4983230072969 + 3 ^ 40 * 2734798 * 2
def baseEnd_2734798 : Nat := 156029540772744035994211

theorem tailTrace_2734798 : CollatzResearch.WordTrace tailWord_2734798 prefixEnd_2734798 156029540772744035994211 := by
  unfold tailWord_2734798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12468284693287673394807631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66497518364200924772307365 12468284693287673394807631)
  ·
    refine ⟨18702427039931510092211447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12468284693287673394807631 18702427039931510092211447)
    ·
      refine ⟨28053640559897265138317171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18702427039931510092211447 28053640559897265138317171)
      ·
        refine ⟨42080460839845897707475757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28053640559897265138317171 42080460839845897707475757)
        ·
          refine ⟨15780172814942211640303409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42080460839845897707475757 15780172814942211640303409)
          ·
            refine ⟨11835129611206658730227557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15780172814942211640303409 11835129611206658730227557)
            ·
              refine ⟨2219086802101248511917667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11835129611206658730227557 2219086802101248511917667)
              ·
                refine ⟨3328630203151872767876501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219086802101248511917667 3328630203151872767876501)
                ·
                  refine ⟨156029540772744035994211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3328630203151872767876501 156029540772744035994211)
                  ·
                    rfl

theorem cell23_2734798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_2734798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734798 prefixEnd_2734798 := by exact prefixLift 2734798
  have htrace : WordTrace (prefixWord ++ tailWord_2734798) baseStart_2734798 baseEnd_2734798 := by
    simpa [prefixWord, tailWord_2734798, baseEnd_2734798] using wordTrace_append hprefix tailTrace_2734798
  have hstable : (prefixWord ++ tailWord_2734798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734798).length < 2 ^ (prefixWord ++ tailWord_2734798).sum := by decide
  have hdescent : baseEnd_2734798 < baseStart_2734798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734841 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 4, 4]
def baseStart_2734841 : Nat := 118140960795 + 2734841 * 2 ^ 59
def prefixEnd_2734841 : Nat := 4983230072969 + 3 ^ 40 * 2734841 * 2
def baseEnd_2734841 : Nat := 468095982207613218570067

theorem tailTrace_2734841 : CollatzResearch.WordTrace tailWord_2734841 prefixEnd_2734841 468095982207613218570067 := by
  unfold tailWord_2734841
  simp only [CollatzResearch.WordTrace]
  refine ⟨99747845885145605502276377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66498563923430403668184251 99747845885145605502276377)
  ·
    refine ⟨74810884413859204126707283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99747845885145605502276377 74810884413859204126707283)
    ·
      refine ⟨112216326620788806190060925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74810884413859204126707283 112216326620788806190060925)
      ·
        refine ⟨42081122482795802321272847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112216326620788806190060925 42081122482795802321272847)
        ·
          refine ⟨63121683724193703481909271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42081122482795802321272847 63121683724193703481909271)
          ·
            refine ⟨94682525586290555222863907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63121683724193703481909271 94682525586290555222863907)
            ·
              refine ⟨142023788379435832834295861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94682525586290555222863907 142023788379435832834295861)
              ·
                refine ⟨13314730160572109328215237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142023788379435832834295861 13314730160572109328215237)
                ·
                  refine ⟨2496511905107270499040357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13314730160572109328215237 2496511905107270499040357)
                  ·
                    refine ⟨468095982207613218570067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496511905107270499040357 468095982207613218570067)
                    ·
                      rfl

theorem cell23_2734841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 4].length) (baseStart_2734841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734841 prefixEnd_2734841 := by exact prefixLift 2734841
  have htrace : WordTrace (prefixWord ++ tailWord_2734841) baseStart_2734841 baseEnd_2734841 := by
    simpa [prefixWord, tailWord_2734841, baseEnd_2734841] using wordTrace_append hprefix tailTrace_2734841
  have hstable : (prefixWord ++ tailWord_2734841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734841).length < 2 ^ (prefixWord ++ tailWord_2734841).sum := by decide
  have hdescent : baseEnd_2734841 < baseStart_2734841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734842 : List Nat := [3, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3]
def baseStart_2734842 : Nat := 118140960795 + 2734842 * 2 ^ 59
def prefixEnd_2734842 : Nat := 4983230072969 + 3 ^ 40 * 2734842 * 2
def baseEnd_2734842 : Nat := 1404288460103494151797697

theorem tailTrace_2734842 : CollatzResearch.WordTrace tailWord_2734842 prefixEnd_2734842 1404288460103494151797697 := by
  unfold tailWord_2734842
  simp only [CollatzResearch.WordTrace]
  refine ⟨24936970589535495668265695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66498588238761321782041853 24936970589535495668265695)
  ·
    refine ⟨37405455884303243502398543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24936970589535495668265695 37405455884303243502398543)
    ·
      refine ⟨56108183826454865253597815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37405455884303243502398543 56108183826454865253597815)
      ·
        refine ⟨84162275739682297880396723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56108183826454865253597815 84162275739682297880396723)
        ·
          refine ⟨126243413609523446820595085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84162275739682297880396723 126243413609523446820595085)
          ·
            refine ⟨47341280103571292557723157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126243413609523446820595085 47341280103571292557723157)
            ·
              refine ⟨2219122504854904338643273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47341280103571292557723157 2219122504854904338643273)
              ·
                refine ⟨1664341878641178253982455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2219122504854904338643273 1664341878641178253982455)
                ·
                  refine ⟨2496512817961767380973683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664341878641178253982455 2496512817961767380973683)
                  ·
                    refine ⟨3744769226942651071460525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2496512817961767380973683 3744769226942651071460525)
                    ·
                      refine ⟨1404288460103494151797697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3744769226942651071460525 1404288460103494151797697)
                      ·
                        rfl

theorem cell23_2734842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3].length) (baseStart_2734842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734842 prefixEnd_2734842 := by exact prefixLift 2734842
  have htrace : WordTrace (prefixWord ++ tailWord_2734842) baseStart_2734842 baseEnd_2734842 := by
    simpa [prefixWord, tailWord_2734842, baseEnd_2734842] using wordTrace_append hprefix tailTrace_2734842
  have hstable : (prefixWord ++ tailWord_2734842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734842).length < 2 ^ (prefixWord ++ tailWord_2734842).sum := by decide
  have hdescent : baseEnd_2734842 < baseStart_2734842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734858 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_2734858 : Nat := 118140960795 + 2734858 * 2 ^ 59
def prefixEnd_2734858 : Nat := 4983230072969 + 3 ^ 40 * 2734858 * 2
def baseEnd_2734858 : Nat := 468098891931322029732541

theorem tailTrace_2734858 : CollatzResearch.WordTrace tailWord_2734858 prefixEnd_2734858 468098891931322029732541 := by
  unfold tailWord_2734858
  simp only [CollatzResearch.WordTrace]
  refine ⟨24937116481521004351411307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66498977284056011603763485 24937116481521004351411307)
  ·
    refine ⟨37405674722281506527116961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24937116481521004351411307 37405674722281506527116961)
    ·
      refine ⟨28054256041711129895337721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37405674722281506527116961 28054256041711129895337721)
      ·
        refine ⟨21040692031283347421503291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28054256041711129895337721 21040692031283347421503291)
        ·
          refine ⟨31561038046925021132254937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21040692031283347421503291 31561038046925021132254937)
          ·
            refine ⟨23670778535193765849191203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31561038046925021132254937 23670778535193765849191203)
            ·
              refine ⟨35506167802790648773786805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23670778535193765849191203 35506167802790648773786805)
              ·
                refine ⟨3328703231511623322542513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35506167802790648773786805 3328703231511623322542513)
                ·
                  refine ⟨2496527423633717491906885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3328703231511623322542513 2496527423633717491906885)
                  ·
                    refine ⟨468098891931322029732541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496527423633717491906885 468098891931322029732541)
                    ·
                      rfl

theorem cell23_2734858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_2734858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734858 prefixEnd_2734858 := by exact prefixLift 2734858
  have htrace : WordTrace (prefixWord ++ tailWord_2734858) baseStart_2734858 baseEnd_2734858 := by
    simpa [prefixWord, tailWord_2734858, baseEnd_2734858] using wordTrace_append hprefix tailTrace_2734858
  have hstable : (prefixWord ++ tailWord_2734858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734858).length < 2 ^ (prefixWord ++ tailWord_2734858).sum := by decide
  have hdescent : baseEnd_2734858 < baseStart_2734858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734882 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_2734882 : Nat := 118140960795 + 2734882 * 2 ^ 59
def prefixEnd_2734882 : Nat := 4983230072969 + 3 ^ 40 * 2734882 * 2
def baseEnd_2734882 : Nat := 1404308999329673995297513

theorem tailTrace_2734882 : CollatzResearch.WordTrace tailWord_2734882 prefixEnd_2734882 1404308999329673995297513 := by
  unfold tailWord_2734882
  simp only [CollatzResearch.WordTrace]
  refine ⟨24937335319499267376129725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66499560851998046336345933 24937335319499267376129725)
  ·
    refine ⟨9351500744812225266048647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24937335319499267376129725 9351500744812225266048647)
    ·
      refine ⟨14027251117218337899072971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9351500744812225266048647 14027251117218337899072971)
      ·
        refine ⟨21040876675827506848609457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14027251117218337899072971 21040876675827506848609457)
        ·
          refine ⟨15780657506870630136457093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21040876675827506848609457 15780657506870630136457093)
          ·
            refine ⟨2958873282538243150585705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15780657506870630136457093 2958873282538243150585705)
            ·
              refine ⟨2219154961903682362939279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2958873282538243150585705 2219154961903682362939279)
              ·
                refine ⟨3328732442855523544408919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219154961903682362939279 3328732442855523544408919)
                ·
                  refine ⟨4993098664283285316613379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3328732442855523544408919 4993098664283285316613379)
                  ·
                    refine ⟨7489647996424927974920069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4993098664283285316613379 7489647996424927974920069)
                    ·
                      refine ⟨1404308999329673995297513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7489647996424927974920069 1404308999329673995297513)
                      ·
                        rfl

theorem cell23_2734882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_2734882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734882 prefixEnd_2734882 := by exact prefixLift 2734882
  have htrace : WordTrace (prefixWord ++ tailWord_2734882) baseStart_2734882 baseEnd_2734882 := by
    simpa [prefixWord, tailWord_2734882, baseEnd_2734882] using wordTrace_append hprefix tailTrace_2734882
  have hstable : (prefixWord ++ tailWord_2734882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734882).length < 2 ^ (prefixWord ++ tailWord_2734882).sum := by decide
  have hdescent : baseEnd_2734882 < baseStart_2734882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734955 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 4, 2, 2]
def baseStart_2734955 : Nat := 118140960795 + 2734955 * 2 ^ 59
def prefixEnd_2734955 : Nat := 4983230072969 + 3 ^ 40 * 2734955 * 2
def baseEnd_2734955 : Nat := 1404346483417452209684677

theorem tailTrace_2734955 : CollatzResearch.WordTrace tailWord_2734955 prefixEnd_2734955 1404346483417452209684677 := by
  unfold tailWord_2734955
  simp only [CollatzResearch.WordTrace]
  refine ⟨99752003806732602971926319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66501335871155068647950879 99752003806732602971926319)
  ·
    refine ⟨149628005710098904457889479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99752003806732602971926319 149628005710098904457889479)
    ·
      refine ⟨224442008565148356686834219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149628005710098904457889479 224442008565148356686834219)
      ·
        refine ⟨336663012847722535030251329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224442008565148356686834219 336663012847722535030251329)
        ·
          refine ⟨252497259635791901272688497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336663012847722535030251329 252497259635791901272688497)
          ·
            refine ⟨189372944726843925954516373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252497259635791901272688497 189372944726843925954516373)
            ·
              refine ⟨8876856784070809029117955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189372944726843925954516373 8876856784070809029117955)
              ·
                refine ⟨13315285176106213543676933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8876856784070809029117955 13315285176106213543676933)
                ·
                  refine ⟨2496615970519915039439425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13315285176106213543676933 2496615970519915039439425)
                  ·
                    refine ⟨1872461977889936279579569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2496615970519915039439425 1872461977889936279579569)
                    ·
                      refine ⟨1404346483417452209684677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872461977889936279579569 1404346483417452209684677)
                      ·
                        rfl

theorem cell23_2734955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 2, 2].length) (baseStart_2734955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734955 prefixEnd_2734955 := by exact prefixLift 2734955
  have htrace : WordTrace (prefixWord ++ tailWord_2734955) baseStart_2734955 baseEnd_2734955 := by
    simpa [prefixWord, tailWord_2734955, baseEnd_2734955] using wordTrace_append hprefix tailTrace_2734955
  have hstable : (prefixWord ++ tailWord_2734955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734955).length < 2 ^ (prefixWord ++ tailWord_2734955).sum := by decide
  have hdescent : baseEnd_2734955 < baseStart_2734955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2734966 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2734966 : Nat := 118140960795 + 2734966 * 2 ^ 59
def prefixEnd_2734966 : Nat := 4983230072969 + 3 ^ 40 * 2734966 * 2
def baseEnd_2734966 : Nat := 1404352131704651666647127

theorem tailTrace_2734966 : CollatzResearch.WordTrace tailWord_2734966 prefixEnd_2734966 1404352131704651666647127 := by
  unfold tailWord_2734966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234525313105796990661047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66501603339795167900384501 6234525313105796990661047)
  ·
    refine ⟨9351787969658695485991571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6234525313105796990661047 9351787969658695485991571)
    ·
      refine ⟨14027681954488043228987357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9351787969658695485991571 14027681954488043228987357)
      ·
        refine ⟨5260380732933016210870259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14027681954488043228987357 5260380732933016210870259)
        ·
          refine ⟨7890571099399524316305389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260380732933016210870259 7890571099399524316305389)
          ·
            refine ⟨2958964162274821618614521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7890571099399524316305389 2958964162274821618614521)
            ·
              refine ⟨2219223121706116213960891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2958964162274821618614521 2219223121706116213960891)
              ·
                refine ⟨3328834682559174320941337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219223121706116213960891 3328834682559174320941337)
                ·
                  refine ⟨2496626011919380740706003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3328834682559174320941337 2496626011919380740706003)
                  ·
                    refine ⟨3744939017879071111059005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2496626011919380740706003 3744939017879071111059005)
                    ·
                      refine ⟨1404352131704651666647127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3744939017879071111059005 1404352131704651666647127)
                      ·
                        rfl

theorem cell23_2734966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2734966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2734966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2734966 prefixEnd_2734966 := by exact prefixLift 2734966
  have htrace : WordTrace (prefixWord ++ tailWord_2734966) baseStart_2734966 baseEnd_2734966 := by
    simpa [prefixWord, tailWord_2734966, baseEnd_2734966] using wordTrace_append hprefix tailTrace_2734966
  have hstable : (prefixWord ++ tailWord_2734966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2734966).length < 2 ^ (prefixWord ++ tailWord_2734966).sum := by decide
  have hdescent : baseEnd_2734966 < baseStart_2734966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2734966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735008 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 2, 5]
def baseStart_2735008 : Nat := 118140960795 + 2735008 * 2 ^ 59
def prefixEnd_2735008 : Nat := 4983230072969 + 3 ^ 40 * 2735008 * 2
def baseEnd_2735008 : Nat := 468124565964046834107311

theorem tailTrace_2735008 : CollatzResearch.WordTrace tailWord_2735008 prefixEnd_2735008 468124565964046834107311 := by
  unfold tailWord_2735008
  simp only [CollatzResearch.WordTrace]
  refine ⟨49876968437770296511802839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66502624583693728682403785 49876968437770296511802839)
  ·
    refine ⟨74815452656655444767704259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49876968437770296511802839 74815452656655444767704259)
    ·
      refine ⟨112223178984983167151556389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74815452656655444767704259 112223178984983167151556389)
      ·
        refine ⟨21041846059684343840916823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112223178984983167151556389 21041846059684343840916823)
        ·
          refine ⟨31562769089526515761375235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21041846059684343840916823 31562769089526515761375235)
          ·
            refine ⟨47344153634289773642062853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31562769089526515761375235 47344153634289773642062853)
            ·
              refine ⟨8877028806429332557886785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47344153634289773642062853 8877028806429332557886785)
              ·
                refine ⟨6657771604821999418415089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8877028806429332557886785 6657771604821999418415089)
                ·
                  refine ⟨4993328703616499563811317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6657771604821999418415089 4993328703616499563811317)
                  ·
                    refine ⟨468124565964046834107311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4993328703616499563811317 468124565964046834107311)
                    ·
                      rfl

theorem cell23_2735008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_2735008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735008 prefixEnd_2735008 := by exact prefixLift 2735008
  have htrace : WordTrace (prefixWord ++ tailWord_2735008) baseStart_2735008 baseEnd_2735008 := by
    simpa [prefixWord, tailWord_2735008, baseEnd_2735008] using wordTrace_append hprefix tailTrace_2735008
  have hstable : (prefixWord ++ tailWord_2735008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735008).length < 2 ^ (prefixWord ++ tailWord_2735008).sum := by decide
  have hdescent : baseEnd_2735008 < baseStart_2735008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735098 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_2735098 : Nat := 118140960795 + 2735098 * 2 ^ 59
def prefixEnd_2735098 : Nat := 4983230072969 + 3 ^ 40 * 2735098 * 2
def baseEnd_2735098 : Nat := 468139970383681716732173

theorem tailTrace_2735098 : CollatzResearch.WordTrace tailWord_2735098 prefixEnd_2735098 468139970383681716732173 := by
  unfold tailWord_2735098
  simp only [CollatzResearch.WordTrace]
  refine ⟨24939304861303634598595487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66504812963476358929587965 24939304861303634598595487)
  ·
    refine ⟨37408957291955451897893231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24939304861303634598595487 37408957291955451897893231)
    ·
      refine ⟨56113435937933177846839847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37408957291955451897893231 56113435937933177846839847)
      ·
        refine ⟨84170153906899766770259771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56113435937933177846839847 84170153906899766770259771)
        ·
          refine ⟨126255230860349650155389657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84170153906899766770259771 126255230860349650155389657)
          ·
            refine ⟨94691423145262237616542243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126255230860349650155389657 94691423145262237616542243)
            ·
              refine ⟨142037134717893356424813365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94691423145262237616542243 142037134717893356424813365)
              ·
                refine ⟨13315981379802502164826253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142037134717893356424813365 13315981379802502164826253)
                ·
                  refine ⟨4993493017425938311809845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13315981379802502164826253 4993493017425938311809845)
                  ·
                    refine ⟨468139970383681716732173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4993493017425938311809845 468139970383681716732173)
                    ·
                      rfl

theorem cell23_2735098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_2735098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735098 prefixEnd_2735098 := by exact prefixLift 2735098
  have htrace : WordTrace (prefixWord ++ tailWord_2735098) baseStart_2735098 baseEnd_2735098 := by
    simpa [prefixWord, tailWord_2735098, baseEnd_2735098] using wordTrace_append hprefix tailTrace_2735098
  have hstable : (prefixWord ++ tailWord_2735098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735098).length < 2 ^ (prefixWord ++ tailWord_2735098).sum := by decide
  have hdescent : baseEnd_2735098 < baseStart_2735098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735115 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 1, 5]
def baseStart_2735115 : Nat := 118140960795 + 2735115 * 2 ^ 59
def prefixEnd_2735115 : Nat := 4983230072969 + 3 ^ 40 * 2735115 * 2
def baseEnd_2735115 : Nat := 468142880107390527894647

theorem tailTrace_2735115 : CollatzResearch.WordTrace tailWord_2735115 prefixEnd_2735115 468142880107390527894647 := by
  unfold tailWord_2735115
  simp only [CollatzResearch.WordTrace]
  refine ⟨99757839486152950297750799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66505226324101966865167199 99757839486152950297750799)
  ·
    refine ⟨149636759229229425446626199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99757839486152950297750799 149636759229229425446626199)
    ·
      refine ⟨224455138843844138169939299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149636759229229425446626199 224455138843844138169939299)
      ·
        refine ⟨336682708265766207254908949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224455138843844138169939299 336682708265766207254908949)
        ·
          refine ⟨15782001949957790965073857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 336682708265766207254908949 15782001949957790965073857)
          ·
            refine ⟨11836501462468343223805393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15782001949957790965073857 11836501462468343223805393)
            ·
              refine ⟨8877376096851257417854045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11836501462468343223805393 8877376096851257417854045)
              ·
                refine ⟨3329016036319221531695267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8877376096851257417854045 3329016036319221531695267)
                ·
                  refine ⟨4993524054478832297542901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329016036319221531695267 4993524054478832297542901)
                  ·
                    refine ⟨468142880107390527894647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4993524054478832297542901 468142880107390527894647)
                    ·
                      rfl

theorem cell23_2735115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 5].length) (baseStart_2735115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735115 prefixEnd_2735115 := by exact prefixLift 2735115
  have htrace : WordTrace (prefixWord ++ tailWord_2735115) baseStart_2735115 baseEnd_2735115 := by
    simpa [prefixWord, tailWord_2735115, baseEnd_2735115] using wordTrace_append hprefix tailTrace_2735115
  have hstable : (prefixWord ++ tailWord_2735115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735115).length < 2 ^ (prefixWord ++ tailWord_2735115).sum := by decide
  have hdescent : baseEnd_2735115 < baseStart_2735115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735136 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 6]
def baseStart_2735136 : Nat := 118140960795 + 2735136 * 2 ^ 59
def prefixEnd_2735136 : Nat := 4983230072969 + 3 ^ 40 * 2735136 * 2
def baseEnd_2735136 : Nat := 156048824823990666835705

theorem tailTrace_2735136 : CollatzResearch.WordTrace tailWord_2735136 prefixEnd_2735136 156048824823990666835705 := by
  unfold tailWord_2735136
  simp only [CollatzResearch.WordTrace]
  refine ⟨49879302709538435442132631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66505736946051247256176841 49879302709538435442132631)
  ·
    refine ⟨74818954064307653163198947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49879302709538435442132631 74818954064307653163198947)
    ·
      refine ⟨112228431096461479744798421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74818954064307653163198947 112228431096461479744798421)
      ·
        refine ⟨2630353853823315931518713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 112228431096461479744798421 2630353853823315931518713)
        ·
          refine ⟨1972765390367486948639035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2630353853823315931518713 1972765390367486948639035)
          ·
            refine ⟨2959148085551230422958553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972765390367486948639035 2959148085551230422958553)
            ·
              refine ⟨2219361064163422817218915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2959148085551230422958553 2219361064163422817218915)
              ·
                refine ⟨3329041596245134225828373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219361064163422817218915 3329041596245134225828373)
                ·
                  refine ⟨156048824823990666835705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3329041596245134225828373 156048824823990666835705)
                  ·
                    rfl

theorem cell23_2735136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 6].length) (baseStart_2735136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735136 prefixEnd_2735136 := by exact prefixLift 2735136
  have htrace : WordTrace (prefixWord ++ tailWord_2735136) baseStart_2735136 baseEnd_2735136 := by
    simpa [prefixWord, tailWord_2735136, baseEnd_2735136] using wordTrace_append hprefix tailTrace_2735136
  have hstable : (prefixWord ++ tailWord_2735136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735136).length < 2 ^ (prefixWord ++ tailWord_2735136).sum := by decide
  have hdescent : baseEnd_2735136 < baseStart_2735136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735148 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_2735148 : Nat := 118140960795 + 2735148 * 2 ^ 59
def prefixEnd_2735148 : Nat := 4983230072969 + 3 ^ 40 * 2735148 * 2
def baseEnd_2735148 : Nat := 1404445585183769954571289

theorem tailTrace_2735148 : CollatzResearch.WordTrace tailWord_2735148 prefixEnd_2735148 1404445585183769954571289 := by
  unfold tailWord_2735148
  simp only [CollatzResearch.WordTrace]
  refine ⟨49879521547516698466851049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66506028730022264622468065 49879521547516698466851049)
  ·
    refine ⟨37409641160637523850138287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49879521547516698466851049 37409641160637523850138287)
    ·
      refine ⟨56114461740956285775207431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37409641160637523850138287 56114461740956285775207431)
      ·
        refine ⟨84171692611434428662811147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56114461740956285775207431 84171692611434428662811147)
        ·
          refine ⟨126257538917151642994216721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84171692611434428662811147 126257538917151642994216721)
          ·
            refine ⟨94693154187863732245662541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126257538917151642994216721 94693154187863732245662541)
            ·
              refine ⟨35509932820448899592123453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94693154187863732245662541 35509932820448899592123453)
              ·
                refine ⟨13316224807668337347046295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35509932820448899592123453 13316224807668337347046295)
                ·
                  refine ⟨19974337211502506020569443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13316224807668337347046295 19974337211502506020569443)
                  ·
                    refine ⟨29961505817253759030854165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19974337211502506020569443 29961505817253759030854165)
                    ·
                      refine ⟨1404445585183769954571289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29961505817253759030854165 1404445585183769954571289)
                      ·
                        rfl

theorem cell23_2735148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_2735148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735148 prefixEnd_2735148 := by exact prefixLift 2735148
  have htrace : WordTrace (prefixWord ++ tailWord_2735148) baseStart_2735148 baseEnd_2735148 := by
    simpa [prefixWord, tailWord_2735148, baseEnd_2735148] using wordTrace_append hprefix tailTrace_2735148
  have hstable : (prefixWord ++ tailWord_2735148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735148).length < 2 ^ (prefixWord ++ tailWord_2735148).sum := by decide
  have hdescent : baseEnd_2735148 < baseStart_2735148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735152 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 5, 2, 2]
def baseStart_2735152 : Nat := 118140960795 + 2735152 * 2 ^ 59
def prefixEnd_2735152 : Nat := 4983230072969 + 3 ^ 40 * 2735152 * 2
def baseEnd_2735152 : Nat := 1404447639106387938921271

theorem tailTrace_2735152 : CollatzResearch.WordTrace tailWord_2735152 prefixEnd_2735152 1404447639106387938921271 := by
  unfold tailWord_2735152
  simp only [CollatzResearch.WordTrace]
  refine ⟨49879594493509452808423855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66506125991345937077898473 49879594493509452808423855)
  ·
    refine ⟨74819391740264179212635783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49879594493509452808423855 74819391740264179212635783)
    ·
      refine ⟨112229087610396268818953675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74819391740264179212635783 112229087610396268818953675)
      ·
        refine ⟨168343631415594403228430513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112229087610396268818953675 168343631415594403228430513)
        ·
          refine ⟨126257723561695802421322885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168343631415594403228430513 126257723561695802421322885)
          ·
            refine ⟨23673323167817962953998041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126257723561695802421322885 23673323167817962953998041)
            ·
              refine ⟨17754992375863472215498531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23673323167817962953998041 17754992375863472215498531)
              ·
                refine ⟨26632488563795208323247797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17754992375863472215498531 26632488563795208323247797)
                ·
                  refine ⟨2496795802855800780304481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26632488563795208323247797 2496795802855800780304481)
                  ·
                    refine ⟨1872596852141850585228361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2496795802855800780304481 1872596852141850585228361)
                    ·
                      refine ⟨1404447639106387938921271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872596852141850585228361 1404447639106387938921271)
                      ·
                        rfl

theorem cell23_2735152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 2, 2].length) (baseStart_2735152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735152 prefixEnd_2735152 := by exact prefixLift 2735152
  have htrace : WordTrace (prefixWord ++ tailWord_2735152) baseStart_2735152 baseEnd_2735152 := by
    simpa [prefixWord, tailWord_2735152, baseEnd_2735152] using wordTrace_append hprefix tailTrace_2735152
  have hstable : (prefixWord ++ tailWord_2735152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735152).length < 2 ^ (prefixWord ++ tailWord_2735152).sum := by decide
  have hdescent : baseEnd_2735152 < baseStart_2735152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735156 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_2735156 : Nat := 118140960795 + 2735156 * 2 ^ 59
def prefixEnd_2735156 : Nat := 4983230072969 + 3 ^ 40 * 2735156 * 2
def baseEnd_2735156 : Nat := 1404449693029005923271253

theorem tailTrace_2735156 : CollatzResearch.WordTrace tailWord_2735156 prefixEnd_2735156 1404449693029005923271253 := by
  unfold tailWord_2735156
  simp only [CollatzResearch.WordTrace]
  refine ⟨49879667439502207149996661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66506223252669609533328881 49879667439502207149996661)
  ·
    refine ⟨4676218822453331920312187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49879667439502207149996661 4676218822453331920312187)
    ·
      refine ⟨7014328233679997880468281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4676218822453331920312187 7014328233679997880468281)
      ·
        refine ⟨5260746175259998410351211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7014328233679997880468281 5260746175259998410351211)
        ·
          refine ⟨7891119262889997615526817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260746175259998410351211 7891119262889997615526817)
          ·
            refine ⟨5918339447167498211645113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7891119262889997615526817 5918339447167498211645113)
            ·
              refine ⟨4438754585375623658733835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5918339447167498211645113 4438754585375623658733835)
              ·
                refine ⟨6658131878063435488100753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4438754585375623658733835 6658131878063435488100753)
                ·
                  refine ⟨4993598908547576616075565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6658131878063435488100753 4993598908547576616075565)
                  ·
                    refine ⟨1872599590705341231028337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4993598908547576616075565 1872599590705341231028337)
                    ·
                      refine ⟨1404449693029005923271253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872599590705341231028337 1404449693029005923271253)
                      ·
                        rfl

theorem cell23_2735156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_2735156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735156 prefixEnd_2735156 := by exact prefixLift 2735156
  have htrace : WordTrace (prefixWord ++ tailWord_2735156) baseStart_2735156 baseEnd_2735156 := by
    simpa [prefixWord, tailWord_2735156, baseEnd_2735156] using wordTrace_append hprefix tailTrace_2735156
  have hstable : (prefixWord ++ tailWord_2735156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735156).length < 2 ^ (prefixWord ++ tailWord_2735156).sum := by decide
  have hdescent : baseEnd_2735156 < baseStart_2735156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735165 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2735165 : Nat := 118140960795 + 2735165 * 2 ^ 59
def prefixEnd_2735165 : Nat := 4983230072969 + 3 ^ 40 * 2735165 * 2
def baseEnd_2735165 : Nat := 1404454314354896388058711

theorem tailTrace_2735165 : CollatzResearch.WordTrace tailWord_2735165 prefixEnd_2735165 1404454314354896388058711 := by
  unfold tailWord_2735165
  simp only [CollatzResearch.WordTrace]
  refine ⟨99759663135971808837070949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66506442090647872558047299 99759663135971808837070949)
  ·
    refine ⟨18704936837994714156950803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99759663135971808837070949 18704936837994714156950803)
    ·
      refine ⟨28057405256992071235426205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18704936837994714156950803 28057405256992071235426205)
      ·
        refine ⟨10521526971372026713284827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28057405256992071235426205 10521526971372026713284827)
        ·
          refine ⟨15782290457058040069927241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10521526971372026713284827 15782290457058040069927241)
          ·
            refine ⟨11836717842793530052445431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15782290457058040069927241 11836717842793530052445431)
            ·
              refine ⟨17755076764190295078668147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11836717842793530052445431 17755076764190295078668147)
              ·
                refine ⟨26632615146285442618002221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17755076764190295078668147 26632615146285442618002221)
                ·
                  refine ⟨9987230679857040981750833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26632615146285442618002221 9987230679857040981750833)
                  ·
                    refine ⟨7490423009892780736313125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9987230679857040981750833 7490423009892780736313125)
                    ·
                      refine ⟨1404454314354896388058711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7490423009892780736313125 1404454314354896388058711)
                      ·
                        rfl

theorem cell23_2735165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2735165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735165 prefixEnd_2735165 := by exact prefixLift 2735165
  have htrace : WordTrace (prefixWord ++ tailWord_2735165) baseStart_2735165 baseEnd_2735165 := by
    simpa [prefixWord, tailWord_2735165, baseEnd_2735165] using wordTrace_append hprefix tailTrace_2735165
  have hstable : (prefixWord ++ tailWord_2735165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735165).length < 2 ^ (prefixWord ++ tailWord_2735165).sum := by decide
  have hdescent : baseEnd_2735165 < baseStart_2735165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735212 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 3, 3, 2]
def baseStart_2735212 : Nat := 118140960795 + 2735212 * 2 ^ 59
def prefixEnd_2735212 : Nat := 4983230072969 + 3 ^ 40 * 2735212 * 2
def baseEnd_2735212 : Nat := 1404478447945657704170995

theorem tailTrace_2735212 : CollatzResearch.WordTrace tailWord_2735212 prefixEnd_2735212 1404478447945657704170995 := by
  unfold tailWord_2735212
  simp only [CollatzResearch.WordTrace]
  refine ⟨49880688683400767932015945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66507584911201023909354593 49880688683400767932015945)
  ·
    refine ⟨37410516512550575949011959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49880688683400767932015945 37410516512550575949011959)
    ·
      refine ⟨56115774768825863923517939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37410516512550575949011959 56115774768825863923517939)
      ·
        refine ⟨84173662153238795885276909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56115774768825863923517939 84173662153238795885276909)
        ·
          refine ⟨31565123307464548456978841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84173662153238795885276909 31565123307464548456978841)
          ·
            refine ⟨23673842480598411342734131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31565123307464548456978841 23673842480598411342734131)
            ·
              refine ⟨35510763720897617014101197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23673842480598411342734131 35510763720897617014101197)
              ·
                refine ⟨13316536395336606380287949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35510763720897617014101197 13316536395336606380287949)
                ·
                  refine ⟨4993701148251227392607981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13316536395336606380287949 4993701148251227392607981)
                  ·
                    refine ⟨1872637930594210272227993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4993701148251227392607981 1872637930594210272227993)
                    ·
                      refine ⟨1404478447945657704170995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872637930594210272227993 1404478447945657704170995)
                      ·
                        rfl

theorem cell23_2735212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_2735212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735212 prefixEnd_2735212 := by exact prefixLift 2735212
  have htrace : WordTrace (prefixWord ++ tailWord_2735212) baseStart_2735212 baseEnd_2735212 := by
    simpa [prefixWord, tailWord_2735212, baseEnd_2735212] using wordTrace_append hprefix tailTrace_2735212
  have hstable : (prefixWord ++ tailWord_2735212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735212).length < 2 ^ (prefixWord ++ tailWord_2735212).sum := by decide
  have hdescent : baseEnd_2735212 < baseStart_2735212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735229 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_2735229 : Nat := 118140960795 + 2735229 * 2 ^ 59
def prefixEnd_2735229 : Nat := 4983230072969 + 3 ^ 40 * 2735229 * 2
def baseEnd_2735229 : Nat := 1404487177116784137658417

theorem tailTrace_2735229 : CollatzResearch.WordTrace tailWord_2735229 prefixEnd_2735229 1404487177116784137658417 := by
  unfold tailWord_2735229
  simp only [CollatzResearch.WordTrace]
  refine ⟨99761997407739947767400741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66507998271826631844933827 99761997407739947767400741)
  ·
    refine ⟨18705374513951240206387639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99761997407739947767400741 18705374513951240206387639)
    ·
      refine ⟨28058061770926860309581459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18705374513951240206387639 28058061770926860309581459)
      ·
        refine ⟨42087092656390290464372189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28058061770926860309581459 42087092656390290464372189)
        ·
          refine ⟨15782659746146358924139571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42087092656390290464372189 15782659746146358924139571)
          ·
            refine ⟨23673989619219538386209357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15782659746146358924139571 23673989619219538386209357)
            ·
              refine ⟨8877746107207326894828509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23673989619219538386209357 8877746107207326894828509)
              ·
                refine ⟨3329154790202747585560691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8877746107207326894828509 3329154790202747585560691)
                ·
                  refine ⟨4993732185304121378341037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329154790202747585560691 4993732185304121378341037)
                  ·
                    refine ⟨1872649569489045516877889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4993732185304121378341037 1872649569489045516877889)
                    ·
                      refine ⟨1404487177116784137658417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872649569489045516877889 1404487177116784137658417)
                      ·
                        rfl

theorem cell23_2735229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_2735229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735229 prefixEnd_2735229 := by exact prefixLift 2735229
  have htrace : WordTrace (prefixWord ++ tailWord_2735229) baseStart_2735229 baseEnd_2735229 := by
    simpa [prefixWord, tailWord_2735229, baseEnd_2735229] using wordTrace_append hprefix tailTrace_2735229
  have hstable : (prefixWord ++ tailWord_2735229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735229).length < 2 ^ (prefixWord ++ tailWord_2735229).sum := by decide
  have hdescent : baseEnd_2735229 < baseStart_2735229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735230 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2735230 : Nat := 118140960795 + 2735230 * 2 ^ 59
def prefixEnd_2735230 : Nat := 4983230072969 + 3 ^ 40 * 2735230 * 2
def baseEnd_2735230 : Nat := 468162563532479544581971

theorem tailTrace_2735230 : CollatzResearch.WordTrace tailWord_2735230 prefixEnd_2735230 468162563532479544581971 := by
  unfold tailWord_2735230
  simp only [CollatzResearch.WordTrace]
  refine ⟨12470254235092040617273393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66508022587157549958791429 12470254235092040617273393)
  ·
    refine ⟨9352690676319030462955045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12470254235092040617273393 9352690676319030462955045)
    ·
      refine ⟨1753629501809818211804071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9352690676319030462955045 1753629501809818211804071)
      ·
        refine ⟨2630444252714727317706107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753629501809818211804071 2630444252714727317706107)
        ·
          refine ⟨3945666379072090976559161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2630444252714727317706107 3945666379072090976559161)
          ·
            refine ⟨2959249784304068232419371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3945666379072090976559161 2959249784304068232419371)
            ·
              refine ⟨4438874676456102348629057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959249784304068232419371 4438874676456102348629057)
              ·
                refine ⟨3329156007342076761471793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4438874676456102348629057 3329156007342076761471793)
                ·
                  refine ⟨2496867005506557571103845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3329156007342076761471793 2496867005506557571103845)
                  ·
                    refine ⟨468162563532479544581971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2496867005506557571103845 468162563532479544581971)
                    ·
                      rfl

theorem cell23_2735230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2735230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735230 prefixEnd_2735230 := by exact prefixLift 2735230
  have htrace : WordTrace (prefixWord ++ tailWord_2735230) baseStart_2735230 baseEnd_2735230 := by
    simpa [prefixWord, tailWord_2735230, baseEnd_2735230] using wordTrace_append hprefix tailTrace_2735230
  have hstable : (prefixWord ++ tailWord_2735230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735230).length < 2 ^ (prefixWord ++ tailWord_2735230).sum := by decide
  have hdescent : baseEnd_2735230 < baseStart_2735230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735236 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_2735236 : Nat := 118140960795 + 2735236 * 2 ^ 59
def prefixEnd_2735236 : Nat := 4983230072969 + 3 ^ 40 * 2735236 * 2
def baseEnd_2735236 : Nat := 1404490771481365610270885

theorem tailTrace_2735236 : CollatzResearch.WordTrace tailWord_2735236 prefixEnd_2735236 1404490771481365610270885 := by
  unfold tailWord_2735236
  simp only [CollatzResearch.WordTrace]
  refine ⟨49881126359357293981452781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66508168479143058641937041 49881126359357293981452781)
  ·
    refine ⟨18705422384758985243044793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49881126359357293981452781 18705422384758985243044793)
    ·
      refine ⟨14029066788569238932283595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18705422384758985243044793 14029066788569238932283595)
      ·
        refine ⟨21043600182853858398425393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14029066788569238932283595 21043600182853858398425393)
        ·
          refine ⟨15782700137140393798819045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21043600182853858398425393 15782700137140393798819045)
          ·
            refine ⟨2959256275713823837278571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15782700137140393798819045 2959256275713823837278571)
            ·
              refine ⟨4438884413570735755917857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959256275713823837278571 4438884413570735755917857)
              ·
                refine ⟨3329163310178051816938393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4438884413570735755917857 3329163310178051816938393)
                ·
                  refine ⟨2496872482633538862703795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3329163310178051816938393 2496872482633538862703795)
                  ·
                    refine ⟨3745308723950308294055693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2496872482633538862703795 3745308723950308294055693)
                    ·
                      refine ⟨1404490771481365610270885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3745308723950308294055693 1404490771481365610270885)
                      ·
                        rfl

theorem cell23_2735236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_2735236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735236 prefixEnd_2735236 := by exact prefixLift 2735236
  have htrace : WordTrace (prefixWord ++ tailWord_2735236) baseStart_2735236 baseEnd_2735236 := by
    simpa [prefixWord, tailWord_2735236, baseEnd_2735236] using wordTrace_append hprefix tailTrace_2735236
  have hstable : (prefixWord ++ tailWord_2735236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735236).length < 2 ^ (prefixWord ++ tailWord_2735236).sum := by decide
  have hdescent : baseEnd_2735236 < baseStart_2735236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735265 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 7]
def baseStart_2735265 : Nat := 118140960795 + 2735265 * 2 ^ 59
def prefixEnd_2735265 : Nat := 4983230072969 + 3 ^ 40 * 2735265 * 2
def baseEnd_2735265 : Nat := 156056184713371777423139

theorem tailTrace_2735265 : CollatzResearch.WordTrace tailWord_2735265 prefixEnd_2735265 156056184713371777423139 := by
  unfold tailWord_2735265
  simp only [CollatzResearch.WordTrace]
  refine ⟨99763310435609525915711249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66508873623739683943807499 99763310435609525915711249)
  ·
    refine ⟨74822482826707144436783437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99763310435609525915711249 74822482826707144436783437)
    ·
      refine ⟨28058431060015179163793789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74822482826707144436783437 28058431060015179163793789)
      ·
        refine ⟨10521911647505692186422671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28058431060015179163793789 10521911647505692186422671)
        ·
          refine ⟨15782867471258538279634007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10521911647505692186422671 15782867471258538279634007)
          ·
            refine ⟨23674301206887807419451011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15782867471258538279634007 23674301206887807419451011)
            ·
              refine ⟨35511451810331711129176517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23674301206887807419451011 35511451810331711129176517)
              ·
                refine ⟨6658397214437195836720597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35511451810331711129176517 6658397214437195836720597)
                ·
                  refine ⟨156056184713371777423139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6658397214437195836720597 156056184713371777423139)
                  ·
                    rfl

theorem cell23_2735265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 7].length) (baseStart_2735265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735265 prefixEnd_2735265 := by exact prefixLift 2735265
  have htrace : WordTrace (prefixWord ++ tailWord_2735265) baseStart_2735265 baseEnd_2735265 := by
    simpa [prefixWord, tailWord_2735265, baseEnd_2735265] using wordTrace_append hprefix tailTrace_2735265
  have hstable : (prefixWord ++ tailWord_2735265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735265).length < 2 ^ (prefixWord ++ tailWord_2735265).sum := by decide
  have hdescent : baseEnd_2735265 < baseStart_2735265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735295 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 4, 5]
def baseStart_2735295 : Nat := 118140960795 + 2735295 * 2 ^ 59
def prefixEnd_2735295 : Nat := 4983230072969 + 3 ^ 40 * 2735295 * 2
def baseEnd_2735295 : Nat := 468173688946660293144371

theorem tailTrace_2735295 : CollatzResearch.WordTrace tailWord_2735295 prefixEnd_2735295 468173688946660293144371 := by
  unfold tailWord_2735295
  simp only [CollatzResearch.WordTrace]
  refine ⟨99764404625500841039303339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66509603083667227359535559 99764404625500841039303339)
  ·
    refine ⟨149646606938251261558955009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99764404625500841039303339 149646606938251261558955009)
    ·
      refine ⟨112234955203688446169216257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149646606938251261558955009 112234955203688446169216257)
      ·
        refine ⟨84176216402766334626912193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112234955203688446169216257 84176216402766334626912193)
        ·
          refine ⟨63132162302074750970184145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84176216402766334626912193 63132162302074750970184145)
          ·
            refine ⟨47349121726556063227638109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63132162302074750970184145 47349121726556063227638109)
            ·
              refine ⟨17755920647458523710364291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47349121726556063227638109 17755920647458523710364291)
              ·
                refine ⟨26633880971187785565546437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17755920647458523710364291 26633880971187785565546437)
                ·
                  refine ⟨4993852682097709793539957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26633880971187785565546437 4993852682097709793539957)
                  ·
                    refine ⟨468173688946660293144371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4993852682097709793539957 468173688946660293144371)
                    ·
                      rfl

theorem cell23_2735295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_2735295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735295 prefixEnd_2735295 := by exact prefixLift 2735295
  have htrace : WordTrace (prefixWord ++ tailWord_2735295) baseStart_2735295 baseEnd_2735295 := by
    simpa [prefixWord, tailWord_2735295, baseEnd_2735295] using wordTrace_append hprefix tailTrace_2735295
  have hstable : (prefixWord ++ tailWord_2735295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735295).length < 2 ^ (prefixWord ++ tailWord_2735295).sum := by decide
  have hdescent : baseEnd_2735295 < baseStart_2735295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735310 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_2735310 : Nat := 118140960795 + 2735310 * 2 ^ 59
def prefixEnd_2735310 : Nat := 4983230072969 + 3 ^ 40 * 2735310 * 2
def baseEnd_2735310 : Nat := 1404528769049798320745545

theorem tailTrace_2735310 : CollatzResearch.WordTrace tailWord_2735310 prefixEnd_2735310 1404528769049798320745545 := by
  unfold tailWord_2735310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12470618965055812325137423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66509967813630999067399589 12470618965055812325137423)
  ·
    refine ⟨18705928447583718487706135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12470618965055812325137423 18705928447583718487706135)
    ·
      refine ⟨28058892671375577731559203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18705928447583718487706135 28058892671375577731559203)
      ·
        refine ⟨42088339007063366597338805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28058892671375577731559203 42088339007063366597338805)
        ·
          refine ⟨3945781781912190618500513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42088339007063366597338805 3945781781912190618500513)
          ·
            refine ⟨2959336336434142963875385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3945781781912190618500513 2959336336434142963875385)
            ·
              refine ⟨2219502252325607222906539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2959336336434142963875385 2219502252325607222906539)
              ·
                refine ⟨3329253378488410834359809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219502252325607222906539 3329253378488410834359809)
                ·
                  refine ⟨2496940033866308125769857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3329253378488410834359809 2496940033866308125769857)
                  ·
                    refine ⟨1872705025399731094327393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2496940033866308125769857 1872705025399731094327393)
                    ·
                      refine ⟨1404528769049798320745545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872705025399731094327393 1404528769049798320745545)
                      ·
                        rfl

theorem cell23_2735310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_2735310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735310 prefixEnd_2735310 := by exact prefixLift 2735310
  have htrace : WordTrace (prefixWord ++ tailWord_2735310) baseStart_2735310 baseEnd_2735310 := by
    simpa [prefixWord, tailWord_2735310, baseEnd_2735310] using wordTrace_append hprefix tailTrace_2735310
  have hstable : (prefixWord ++ tailWord_2735310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735310).length < 2 ^ (prefixWord ++ tailWord_2735310).sum := by decide
  have hdescent : baseEnd_2735310 < baseStart_2735310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735332 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_2735332 : Nat := 118140960795 + 2735332 * 2 ^ 59
def prefixEnd_2735332 : Nat := 4983230072969 + 3 ^ 40 * 2735332 * 2
def baseEnd_2735332 : Nat := 1404540065624197234670443

theorem tailTrace_2735332 : CollatzResearch.WordTrace tailWord_2735332 prefixEnd_2735332 1404540065624197234670443 := by
  unfold tailWord_2735332
  simp only [CollatzResearch.WordTrace]
  refine ⟨49882877063183398179200125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66510502750911197572266833 49882877063183398179200125)
  ·
    refine ⟨18706078898693774317200047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49882877063183398179200125 18706078898693774317200047)
    ·
      refine ⟨28059118348040661475800071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18706078898693774317200047 28059118348040661475800071)
      ·
        refine ⟨42088677522060992213700107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28059118348040661475800071 42088677522060992213700107)
        ·
          refine ⟨63133016283091488320550161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42088677522060992213700107 63133016283091488320550161)
          ·
            refine ⟨47349762212318616240412621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63133016283091488320550161 47349762212318616240412621)
            ·
              refine ⟨17756160829619481090154733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47349762212318616240412621 17756160829619481090154733)
              ·
                refine ⟨6658560311107305408808025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17756160829619481090154733 6658560311107305408808025)
                ·
                  refine ⟨4993920233330479056606019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6658560311107305408808025 4993920233330479056606019)
                  ·
                    refine ⟨7490880349995718584909029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4993920233330479056606019 7490880349995718584909029)
                    ·
                      refine ⟨1404540065624197234670443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7490880349995718584909029 1404540065624197234670443)
                      ·
                        rfl

theorem cell23_2735332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_2735332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735332 prefixEnd_2735332 := by exact prefixLift 2735332
  have htrace : WordTrace (prefixWord ++ tailWord_2735332) baseStart_2735332 baseEnd_2735332 := by
    simpa [prefixWord, tailWord_2735332, baseEnd_2735332] using wordTrace_append hprefix tailTrace_2735332
  have hstable : (prefixWord ++ tailWord_2735332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735332).length < 2 ^ (prefixWord ++ tailWord_2735332).sum := by decide
  have hdescent : baseEnd_2735332 < baseStart_2735332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735345 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_2735345 : Nat := 118140960795 + 2735345 * 2 ^ 59
def prefixEnd_2735345 : Nat := 4983230072969 + 3 ^ 40 * 2735345 * 2
def baseEnd_2735345 : Nat := 1404546740872705683807883

theorem tailTrace_2735345 : CollatzResearch.WordTrace tailWord_2735345 prefixEnd_2735345 1404546740872705683807883 := by
  unfold tailWord_2735345
  simp only [CollatzResearch.WordTrace]
  refine ⟨99766228275319699578623489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66510818850213133052415659 99766228275319699578623489)
  ·
    refine ⟨74824671206489774683967617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99766228275319699578623489 74824671206489774683967617)
    ·
      refine ⟨56118503404867331012975713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74824671206489774683967617 56118503404867331012975713)
      ·
        refine ⟨42088877553650498259731785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56118503404867331012975713 42088877553650498259731785)
        ·
          refine ⟨31566658165237873694798839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42088877553650498259731785 31566658165237873694798839)
          ·
            refine ⟨47349987247856810542198259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31566658165237873694798839 47349987247856810542198259)
            ·
              refine ⟨71024980871785215813297389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47349987247856810542198259 71024980871785215813297389)
              ·
                refine ⟨26634367826919455929986521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71024980871785215813297389 26634367826919455929986521)
                ·
                  refine ⟨19975775870189591947489891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26634367826919455929986521 19975775870189591947489891)
                  ·
                    refine ⟨29963663805284387921234837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19975775870189591947489891 29963663805284387921234837)
                    ·
                      refine ⟨1404546740872705683807883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29963663805284387921234837 1404546740872705683807883)
                      ·
                        rfl

theorem cell23_2735345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_2735345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735345 prefixEnd_2735345 := by exact prefixLift 2735345
  have htrace : WordTrace (prefixWord ++ tailWord_2735345) baseStart_2735345 baseEnd_2735345 := by
    simpa [prefixWord, tailWord_2735345, baseEnd_2735345] using wordTrace_append hprefix tailTrace_2735345
  have hstable : (prefixWord ++ tailWord_2735345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735345).length < 2 ^ (prefixWord ++ tailWord_2735345).sum := by decide
  have hdescent : baseEnd_2735345 < baseStart_2735345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735372 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 6]
def baseStart_2735372 : Nat := 118140960795 + 2735372 * 2 ^ 59
def prefixEnd_2735372 : Nat := 4983230072969 + 3 ^ 40 * 2735372 * 2
def baseEnd_2735372 : Nat := 156062289427819675352251

theorem tailTrace_2735372 : CollatzResearch.WordTrace tailWord_2735372 prefixEnd_2735372 156062289427819675352251 := by
  unfold tailWord_2735372
  simp only [CollatzResearch.WordTrace]
  refine ⟨49883606523110941594928185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66511475364147922126570913 49883606523110941594928185)
  ·
    refine ⟨37412704892333206196196139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49883606523110941594928185 37412704892333206196196139)
    ·
      refine ⟨56119057338499809294294209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37412704892333206196196139 56119057338499809294294209)
      ·
        refine ⟨42089293003874856970720657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56119057338499809294294209 42089293003874856970720657)
        ·
          refine ⟨31566969752906142728040493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42089293003874856970720657 31566969752906142728040493)
          ·
            refine ⟨11837613657339803523015185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31566969752906142728040493 11837613657339803523015185)
            ·
              refine ⟨8878210243004852642261389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11837613657339803523015185 8878210243004852642261389)
              ·
                refine ⟨3329328841126819740848021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8878210243004852642261389 3329328841126819740848021)
                ·
                  refine ⟨156062289427819675352251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3329328841126819740848021 156062289427819675352251)
                  ·
                    rfl

theorem cell23_2735372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_2735372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735372 prefixEnd_2735372 := by exact prefixLift 2735372
  have htrace : WordTrace (prefixWord ++ tailWord_2735372) baseStart_2735372 baseEnd_2735372 := by
    simpa [prefixWord, tailWord_2735372, baseEnd_2735372] using wordTrace_append hprefix tailTrace_2735372
  have hstable : (prefixWord ++ tailWord_2735372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735372).length < 2 ^ (prefixWord ++ tailWord_2735372).sum := by decide
  have hdescent : baseEnd_2735372 < baseStart_2735372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735386 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3]
def baseStart_2735386 : Nat := 118140960795 + 2735386 * 2 ^ 59
def prefixEnd_2735386 : Nat := 4983230072969 + 3 ^ 40 * 2735386 * 2
def baseEnd_2735386 : Nat := 1404567793579540023395195

theorem tailTrace_2735386 : CollatzResearch.WordTrace tailWord_2735386 prefixEnd_2735386 1404567793579540023395195 := by
  unfold tailWord_2735386
  simp only [CollatzResearch.WordTrace]
  refine ⟨24941930917042790895216503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66511815778780775720577341 24941930917042790895216503)
  ·
    refine ⟨37412896375564186342824755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24941930917042790895216503 37412896375564186342824755)
    ·
      refine ⟨56119344563346279514237133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37412896375564186342824755 56119344563346279514237133)
      ·
        refine ⟨21044754211254854817838925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56119344563346279514237133 21044754211254854817838925)
        ·
          refine ⟨7891782829220570556689597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21044754211254854817838925 7891782829220570556689597)
          ·
            refine ⟨2959418560957713958758599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7891782829220570556689597 2959418560957713958758599)
            ·
              refine ⟨4439127841436570938137899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959418560957713958758599 4439127841436570938137899)
              ·
                refine ⟨6658691762154856407206849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439127841436570938137899 6658691762154856407206849)
                ·
                  refine ⟨4994018821616142305405137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6658691762154856407206849 4994018821616142305405137)
                  ·
                    refine ⟨3745514116212106729053853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4994018821616142305405137 3745514116212106729053853)
                    ·
                      refine ⟨1404567793579540023395195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3745514116212106729053853 1404567793579540023395195)
                      ·
                        rfl

theorem cell23_2735386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_2735386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735386 prefixEnd_2735386 := by exact prefixLift 2735386
  have htrace : WordTrace (prefixWord ++ tailWord_2735386) baseStart_2735386 baseEnd_2735386 := by
    simpa [prefixWord, tailWord_2735386, baseEnd_2735386] using wordTrace_append hprefix tailTrace_2735386
  have hstable : (prefixWord ++ tailWord_2735386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735386).length < 2 ^ (prefixWord ++ tailWord_2735386).sum := by decide
  have hdescent : baseEnd_2735386 < baseStart_2735386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735415 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 2, 10]
def baseStart_2735415 : Nat := 118140960795 + 2735415 * 2 ^ 59
def prefixEnd_2735415 : Nat := 4983230072969 + 3 ^ 40 * 2735415 * 2
def baseEnd_2735415 : Nat := 468194228172840136644187

theorem tailTrace_2735415 : CollatzResearch.WordTrace tailWord_2735415 prefixEnd_2735415 468194228172840136644187 := by
  unfold tailWord_2735415
  simp only [CollatzResearch.WordTrace]
  refine ⟨99768781385066101533671699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66512520923377401022447799 99768781385066101533671699)
  ·
    refine ⟨149653172077599152300507549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99768781385066101533671699 149653172077599152300507549)
    ·
      refine ⟨56119939529099682112690331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149653172077599152300507549 56119939529099682112690331)
      ·
        refine ⟨84179909293649523169035497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56119939529099682112690331 84179909293649523169035497)
        ·
          refine ⟨63134931970237142376776623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84179909293649523169035497 63134931970237142376776623)
          ·
            refine ⟨94702397955355713565164935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63134931970237142376776623 94702397955355713565164935)
            ·
              refine ⟨142053596933033570347747403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94702397955355713565164935 142053596933033570347747403)
              ·
                refine ⟨213080395399550355521621105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142053596933033570347747403 213080395399550355521621105)
                ·
                  refine ⟨159810296549662766641215829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213080395399550355521621105 159810296549662766641215829)
                  ·
                    refine ⟨468194228172840136644187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 159810296549662766641215829 468194228172840136644187)
                    ·
                      rfl

theorem cell23_2735415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_2735415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735415 prefixEnd_2735415 := by exact prefixLift 2735415
  have htrace : WordTrace (prefixWord ++ tailWord_2735415) baseStart_2735415 baseEnd_2735415 := by
    simpa [prefixWord, tailWord_2735415, baseEnd_2735415] using wordTrace_append hprefix tailTrace_2735415
  have hstable : (prefixWord ++ tailWord_2735415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735415).length < 2 ^ (prefixWord ++ tailWord_2735415).sum := by decide
  have hdescent : baseEnd_2735415 < baseStart_2735415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735442 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2735442 : Nat := 118140960795 + 2735442 * 2 ^ 59
def prefixEnd_2735442 : Nat := 4983230072969 + 3 ^ 40 * 2735442 * 2
def baseEnd_2735442 : Nat := 1404596548496191804294937

theorem tailTrace_2735442 : CollatzResearch.WordTrace tailWord_2735442 prefixEnd_2735442 1404596548496191804294937 := by
  unfold tailWord_2735442
  simp only [CollatzResearch.WordTrace]
  refine ⟨24942441538992071286226145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66513177437312190096603053 24942441538992071286226145)
  ·
    refine ⟨18706831154244053464669609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24942441538992071286226145 18706831154244053464669609)
    ·
      refine ⟨14030123365683040098502207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18706831154244053464669609 14030123365683040098502207)
      ·
        refine ⟨21045185048524560147753311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14030123365683040098502207 21045185048524560147753311)
        ·
          refine ⟨31567777572786840221629967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21045185048524560147753311 31567777572786840221629967)
          ·
            refine ⟨47351666359180260332444951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31567777572786840221629967 47351666359180260332444951)
            ·
              refine ⟨71027499538770390498667427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47351666359180260332444951 71027499538770390498667427)
              ·
                refine ⟨106541249308155585748001141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71027499538770390498667427 106541249308155585748001141)
                ·
                  refine ⟨9988242122639586163875107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106541249308155585748001141 9988242122639586163875107)
                  ·
                    refine ⟨14982363183959379245812661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9988242122639586163875107 14982363183959379245812661)
                    ·
                      refine ⟨1404596548496191804294937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14982363183959379245812661 1404596548496191804294937)
                      ·
                        rfl

theorem cell23_2735442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2735442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735442 prefixEnd_2735442 := by exact prefixLift 2735442
  have htrace : WordTrace (prefixWord ++ tailWord_2735442) baseStart_2735442 baseEnd_2735442 := by
    simpa [prefixWord, tailWord_2735442, baseEnd_2735442] using wordTrace_append hprefix tailTrace_2735442
  have hstable : (prefixWord ++ tailWord_2735442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735442).length < 2 ^ (prefixWord ++ tailWord_2735442).sum := by decide
  have hdescent : baseEnd_2735442 < baseStart_2735442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735459 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 5]
def baseStart_2735459 : Nat := 118140960795 + 2735459 * 2 ^ 59
def prefixEnd_2735459 : Nat := 4983230072969 + 3 ^ 40 * 2735459 * 2
def baseEnd_2735459 : Nat := 1404605277667318237782359

theorem tailTrace_2735459 : CollatzResearch.WordTrace tailWord_2735459 prefixEnd_2735459 1404605277667318237782359 := by
  unfold tailWord_2735459
  simp only [CollatzResearch.WordTrace]
  refine ⟨99770386196906697048273431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66513590797937798032182287 99770386196906697048273431)
  ·
    refine ⟨149655579295360045572410147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99770386196906697048273431 149655579295360045572410147)
    ·
      refine ⟨224483368943040068358615221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149655579295360045572410147 224483368943040068358615221)
      ·
        refine ⟨21045315838410006408620177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224483368943040068358615221 21045315838410006408620177)
        ·
          refine ⟨15783986878807504806465133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21045315838410006408620177 15783986878807504806465133)
          ·
            refine ⟨5918995079552814302424425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15783986878807504806465133 5918995079552814302424425)
            ·
              refine ⟨4439246309664610726818319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5918995079552814302424425 4439246309664610726818319)
              ·
                refine ⟨6658869464496916090227479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439246309664610726818319 6658869464496916090227479)
                ·
                  refine ⟨9988304196745374135341219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6658869464496916090227479 9988304196745374135341219)
                  ·
                    refine ⟨14982456295118061203011829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9988304196745374135341219 14982456295118061203011829)
                    ·
                      refine ⟨1404605277667318237782359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14982456295118061203011829 1404605277667318237782359)
                      ·
                        rfl

theorem cell23_2735459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_2735459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735459 prefixEnd_2735459 := by exact prefixLift 2735459
  have htrace : WordTrace (prefixWord ++ tailWord_2735459) baseStart_2735459 baseEnd_2735459 := by
    simpa [prefixWord, tailWord_2735459, baseEnd_2735459] using wordTrace_append hprefix tailTrace_2735459
  have hstable : (prefixWord ++ tailWord_2735459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735459).length < 2 ^ (prefixWord ++ tailWord_2735459).sum := by decide
  have hdescent : baseEnd_2735459 < baseStart_2735459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735473 : List Nat := [1, 2, 2, 2, 1, 2, 2, 6, 1, 2, 2]
def baseStart_2735473 : Nat := 118140960795 + 2735473 * 2 ^ 59
def prefixEnd_2735473 : Nat := 4983230072969 + 3 ^ 40 * 2735473 * 2
def baseEnd_2735473 : Nat := 1404612466396481183007295

theorem tailTrace_2735473 : CollatzResearch.WordTrace tailWord_2735473 prefixEnd_2735473 1404612466396481183007295 := by
  unfold tailWord_2735473
  simp only [CollatzResearch.WordTrace]
  refine ⟨99770896818855977439283073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66513931212570651626188715 99770896818855977439283073)
  ·
    refine ⟨74828172614141983079462305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99770896818855977439283073 74828172614141983079462305)
    ·
      refine ⟨56121129460606487309596729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74828172614141983079462305 56121129460606487309596729)
      ·
        refine ⟨42090847095454865482197547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56121129460606487309596729 42090847095454865482197547)
        ·
          refine ⟨63136270643182298223296321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42090847095454865482197547 63136270643182298223296321)
          ·
            refine ⟨47352202982386723667472241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63136270643182298223296321 47352202982386723667472241)
            ·
              refine ⟨35514152236790042750604181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47352202982386723667472241 35514152236790042750604181)
              ·
                refine ⟨1664725886099533253934571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35514152236790042750604181 1664725886099533253934571)
                ·
                  refine ⟨2497088829149299880901857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664725886099533253934571 2497088829149299880901857)
                  ·
                    refine ⟨1872816621861974910676393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2497088829149299880901857 1872816621861974910676393)
                    ·
                      refine ⟨1404612466396481183007295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872816621861974910676393 1404612466396481183007295)
                      ·
                        rfl

theorem cell23_2735473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_2735473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735473 prefixEnd_2735473 := by exact prefixLift 2735473
  have htrace : WordTrace (prefixWord ++ tailWord_2735473) baseStart_2735473 baseEnd_2735473 := by
    simpa [prefixWord, tailWord_2735473, baseEnd_2735473] using wordTrace_append hprefix tailTrace_2735473
  have hstable : (prefixWord ++ tailWord_2735473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735473).length < 2 ^ (prefixWord ++ tailWord_2735473).sum := by decide
  have hdescent : baseEnd_2735473 < baseStart_2735473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735490 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2735490 : Nat := 118140960795 + 2735490 * 2 ^ 59
def prefixEnd_2735490 : Nat := 4983230072969 + 3 ^ 40 * 2735490 * 2
def baseEnd_2735490 : Nat := 1404621195567607616494717

theorem tailTrace_2735490 : CollatzResearch.WordTrace tailWord_2735490 prefixEnd_2735490 1404621195567607616494717 := by
  unfold tailWord_2735490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24942879214948597335662981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66514344573196259561767949 24942879214948597335662981)
  ·
    refine ⟨4676789852802862000436809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24942879214948597335662981 4676789852802862000436809)
    ·
      refine ⟨3507592389602146500327607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4676789852802862000436809 3507592389602146500327607)
      ·
        refine ⟨5261388584403219750491411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507592389602146500327607 5261388584403219750491411)
        ·
          refine ⟨7892082876604829625737117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261388584403219750491411 7892082876604829625737117)
          ·
            refine ⟨2959531078726811109651419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7892082876604829625737117 2959531078726811109651419)
            ·
              refine ⟨4439296618090216664477129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959531078726811109651419 4439296618090216664477129)
              ·
                refine ⟨3329472463567662498357847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4439296618090216664477129 3329472463567662498357847)
                ·
                  refine ⟨4994208695351493747536771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329472463567662498357847 4994208695351493747536771)
                  ·
                    refine ⟨7491313043027240621305157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4994208695351493747536771 7491313043027240621305157)
                    ·
                      refine ⟨1404621195567607616494717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7491313043027240621305157 1404621195567607616494717)
                      ·
                        rfl

theorem cell23_2735490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2735490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735490 prefixEnd_2735490 := by exact prefixLift 2735490
  have htrace : WordTrace (prefixWord ++ tailWord_2735490) baseStart_2735490 baseEnd_2735490 := by
    simpa [prefixWord, tailWord_2735490, baseEnd_2735490] using wordTrace_append hprefix tailTrace_2735490
  have hstable : (prefixWord ++ tailWord_2735490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735490).length < 2 ^ (prefixWord ++ tailWord_2735490).sum := by decide
  have hdescent : baseEnd_2735490 < baseStart_2735490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735532 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2735532 : Nat := 118140960795 + 2735532 * 2 ^ 59
def prefixEnd_2735532 : Nat := 4983230072969 + 3 ^ 40 * 2735532 * 2
def baseEnd_2735532 : Nat := 1404642761755096452169523

theorem tailTrace_2735532 : CollatzResearch.WordTrace tailWord_2735532 prefixEnd_2735532 1404642761755096452169523 := by
  unfold tailWord_2735532
  simp only [CollatzResearch.WordTrace]
  refine ⟨49886524362821115257840425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66515365817094820343787233 49886524362821115257840425)
  ·
    refine ⟨37414893272115836443380319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49886524362821115257840425 37414893272115836443380319)
    ·
      refine ⟨56122339908173754665070479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37414893272115836443380319 56122339908173754665070479)
      ·
        refine ⟨84183509862260631997605719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56122339908173754665070479 84183509862260631997605719)
        ·
          refine ⟨126275264793390947996408579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84183509862260631997605719 126275264793390947996408579)
          ·
            refine ⟨189412897190086421994612869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126275264793390947996408579 189412897190086421994612869)
            ·
              refine ⟨35514918223141204123989913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189412897190086421994612869 35514918223141204123989913)
              ·
                refine ⟨26636188667355903092992435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35514918223141204123989913 26636188667355903092992435)
                ·
                  refine ⟨39954283001033854639488653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26636188667355903092992435 39954283001033854639488653)
                  ·
                    refine ⟨14982856125387695489808245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39954283001033854639488653 14982856125387695489808245)
                    ·
                      refine ⟨1404642761755096452169523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14982856125387695489808245 1404642761755096452169523)
                      ·
                        rfl

theorem cell23_2735532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2735532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735532 prefixEnd_2735532 := by exact prefixLift 2735532
  have htrace : WordTrace (prefixWord ++ tailWord_2735532) baseStart_2735532 baseEnd_2735532 := by
    simpa [prefixWord, tailWord_2735532, baseEnd_2735532] using wordTrace_append hprefix tailTrace_2735532
  have hstable : (prefixWord ++ tailWord_2735532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735532).length < 2 ^ (prefixWord ++ tailWord_2735532).sum := by decide
  have hdescent : baseEnd_2735532 < baseStart_2735532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735533 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_2735533 : Nat := 118140960795 + 2735533 * 2 ^ 59
def prefixEnd_2735533 : Nat := 4983230072969 + 3 ^ 40 * 2735533 * 2
def baseEnd_2735533 : Nat := 1404643275235750948257019

theorem tailTrace_2735533 : CollatzResearch.WordTrace tailWord_2735533 prefixEnd_2735533 1404643275235750948257019 := by
  unfold tailWord_2735533
  simp only [CollatzResearch.WordTrace]
  refine ⟨99773085198638607686467253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66515390132425738457644835 99773085198638607686467253)
  ·
    refine ⟨9353726737372369470606305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99773085198638607686467253 9353726737372369470606305)
    ·
      refine ⟨7015295053029277102954729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9353726737372369470606305 7015295053029277102954729)
      ·
        refine ⟨5261471289771957827216047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7015295053029277102954729 5261471289771957827216047)
        ·
          refine ⟨7892206934657936740824071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261471289771957827216047 7892206934657936740824071)
          ·
            refine ⟨11838310401986905111236107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7892206934657936740824071 11838310401986905111236107)
            ·
              refine ⟨17757465602980357666854161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11838310401986905111236107 17757465602980357666854161)
              ·
                refine ⟨13318099202235268250140621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17757465602980357666854161 13318099202235268250140621)
                ·
                  refine ⟨4994287200838225593802733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13318099202235268250140621 4994287200838225593802733)
                  ·
                    refine ⟨1872857700314334597676025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4994287200838225593802733 1872857700314334597676025)
                    ·
                      refine ⟨1404643275235750948257019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872857700314334597676025 1404643275235750948257019)
                      ·
                        rfl

theorem cell23_2735533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_2735533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735533 prefixEnd_2735533 := by exact prefixLift 2735533
  have htrace : WordTrace (prefixWord ++ tailWord_2735533) baseStart_2735533 baseEnd_2735533 := by
    simpa [prefixWord, tailWord_2735533, baseEnd_2735533] using wordTrace_append hprefix tailTrace_2735533
  have hstable : (prefixWord ++ tailWord_2735533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735533).length < 2 ^ (prefixWord ++ tailWord_2735533).sum := by decide
  have hdescent : baseEnd_2735533 < baseStart_2735533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735546 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2]
def baseStart_2735546 : Nat := 118140960795 + 2735546 * 2 ^ 59
def prefixEnd_2735546 : Nat := 4983230072969 + 3 ^ 40 * 2735546 * 2
def baseEnd_2735546 : Nat := 1404649950484259397394459

theorem tailTrace_2735546 : CollatzResearch.WordTrace tailWord_2735546 prefixEnd_2735546 1404649950484259397394459 := by
  unfold tailWord_2735546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24943389836897877726672623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66515706231727673937793661 24943389836897877726672623)
  ·
    refine ⟨37415084755346816590008935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24943389836897877726672623 37415084755346816590008935)
    ·
      refine ⟨56122627133020224885013403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37415084755346816590008935 56122627133020224885013403)
      ·
        refine ⟨84183940699530337327520105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56122627133020224885013403 84183940699530337327520105)
        ·
          refine ⟨63137955524647752995640079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84183940699530337327520105 63137955524647752995640079)
          ·
            refine ⟨94706933286971629493460119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63137955524647752995640079 94706933286971629493460119)
            ·
              refine ⟨142060399930457444240190179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94706933286971629493460119 142060399930457444240190179)
              ·
                refine ⟨213090599895686166360285269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142060399930457444240190179 213090599895686166360285269)
                ·
                  refine ⟨2497155467527572262034593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 213090599895686166360285269 2497155467527572262034593)
                  ·
                    refine ⟨1872866600645679196525945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2497155467527572262034593 1872866600645679196525945)
                    ·
                      refine ⟨1404649950484259397394459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872866600645679196525945 1404649950484259397394459)
                      ·
                        rfl

theorem cell23_2735546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_2735546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735546 prefixEnd_2735546 := by exact prefixLift 2735546
  have htrace : WordTrace (prefixWord ++ tailWord_2735546) baseStart_2735546 baseEnd_2735546 := by
    simpa [prefixWord, tailWord_2735546, baseEnd_2735546] using wordTrace_append hprefix tailTrace_2735546
  have hstable : (prefixWord ++ tailWord_2735546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735546).length < 2 ^ (prefixWord ++ tailWord_2735546).sum := by decide
  have hdescent : baseEnd_2735546 < baseStart_2735546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735549 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_2735549 : Nat := 118140960795 + 2735549 * 2 ^ 59
def prefixEnd_2735549 : Nat := 4983230072969 + 3 ^ 40 * 2735549 * 2
def baseEnd_2735549 : Nat := 1404651490926222885656945

theorem tailTrace_2735549 : CollatzResearch.WordTrace tailWord_2735549 prefixEnd_2735549 1404651490926222885656945 := by
  unfold tailWord_2735549
  simp only [CollatzResearch.WordTrace]
  refine ⟨99773668766580642419049701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66515779177720428279366467 99773668766580642419049701)
  ·
    refine ⟨18707562893733870453571819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99773668766580642419049701 18707562893733870453571819)
    ·
      refine ⟨28061344340600805680357729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18707562893733870453571819 28061344340600805680357729)
      ·
        refine ⟨21046008255450604260268297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28061344340600805680357729 21046008255450604260268297)
        ·
          refine ⟨15784506191587953195201223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21046008255450604260268297 15784506191587953195201223)
          ·
            refine ⟨23676759287381929792801835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15784506191587953195201223 23676759287381929792801835)
            ·
              refine ⟨35515138931072894689202753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23676759287381929792801835 35515138931072894689202753)
              ·
                refine ⟨26636354198304671016902065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35515138931072894689202753 26636354198304671016902065)
                ·
                  refine ⟨19977265648728503262676549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26636354198304671016902065 19977265648728503262676549)
                  ·
                    refine ⟨3745737309136594361751853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19977265648728503262676549 3745737309136594361751853)
                    ·
                      refine ⟨1404651490926222885656945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3745737309136594361751853 1404651490926222885656945)
                      ·
                        rfl

theorem cell23_2735549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_2735549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735549 prefixEnd_2735549 := by exact prefixLift 2735549
  have htrace : WordTrace (prefixWord ++ tailWord_2735549) baseStart_2735549 baseEnd_2735549 := by
    simpa [prefixWord, tailWord_2735549, baseEnd_2735549] using wordTrace_append hprefix tailTrace_2735549
  have hstable : (prefixWord ++ tailWord_2735549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735549).length < 2 ^ (prefixWord ++ tailWord_2735549).sum := by decide
  have hdescent : baseEnd_2735549 < baseStart_2735549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735552 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 9]
def baseStart_2735552 : Nat := 118140960795 + 2735552 * 2 ^ 59
def prefixEnd_2735552 : Nat := 4983230072969 + 3 ^ 40 * 2735552 * 2
def baseEnd_2735552 : Nat := 156072559040909597102159

theorem tailTrace_2735552 : CollatzResearch.WordTrace tailWord_2735552 prefixEnd_2735552 156072559040909597102159 := by
  unfold tailWord_2735552
  simp only [CollatzResearch.WordTrace]
  refine ⟨49886889092784886965704455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66515852123713182620939273 49886889092784886965704455)
  ·
    refine ⟨74830333639177330448556683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49886889092784886965704455 74830333639177330448556683)
    ·
      refine ⟨112245500458765995672835025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74830333639177330448556683 112245500458765995672835025)
      ·
        refine ⟨84184125344074496754626269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112245500458765995672835025 84184125344074496754626269)
        ·
          refine ⟨31569047004027936282984851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84184125344074496754626269 31569047004027936282984851)
          ·
            refine ⟨47353570506041904424477277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31569047004027936282984851 47353570506041904424477277)
            ·
              refine ⟨17757588939765714159178979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47353570506041904424477277 17757588939765714159178979)
              ·
                refine ⟨26636383409648571238768469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17757588939765714159178979 26636383409648571238768469)
                ·
                  refine ⟨156072559040909597102159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26636383409648571238768469 156072559040909597102159)
                  ·
                    rfl

theorem cell23_2735552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 9].length) (baseStart_2735552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735552 prefixEnd_2735552 := by exact prefixLift 2735552
  have htrace : WordTrace (prefixWord ++ tailWord_2735552) baseStart_2735552 baseEnd_2735552 := by
    simpa [prefixWord, tailWord_2735552, baseEnd_2735552] using wordTrace_append hprefix tailTrace_2735552
  have hstable : (prefixWord ++ tailWord_2735552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735552).length < 2 ^ (prefixWord ++ tailWord_2735552).sum := by decide
  have hdescent : baseEnd_2735552 < baseStart_2735552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735597 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_2735597 : Nat := 118140960795 + 2735597 * 2 ^ 59
def prefixEnd_2735597 : Nat := 4983230072969 + 3 ^ 40 * 2735597 * 2
def baseEnd_2735597 : Nat := 1404676137997638697856725

theorem tailTrace_2735597 : CollatzResearch.WordTrace tailWord_2735597 prefixEnd_2735597 1404676137997638697856725 := by
  unfold tailWord_2735597
  simp only [CollatzResearch.WordTrace]
  refine ⟨99775419470406746616797045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66516946313604497744531363 99775419470406746616797045)
  ·
    refine ⟨9353945575350632495324723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99775419470406746616797045 9353945575350632495324723)
    ·
      refine ⟨14030918363025948742987085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9353945575350632495324723 14030918363025948742987085)
      ·
        refine ⟨5261594386134730778620157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14030918363025948742987085 5261594386134730778620157)
        ·
          refine ⟨1973097894800524041982559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5261594386134730778620157 1973097894800524041982559)
          ·
            refine ⟨2959646842200786062973839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973097894800524041982559 2959646842200786062973839)
            ·
              refine ⟨4439470263301179094460759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959646842200786062973839 4439470263301179094460759)
              ·
                refine ⟨6659205394951768641691139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439470263301179094460759 6659205394951768641691139)
                ·
                  refine ⟨9988808092427652962536709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6659205394951768641691139 9988808092427652962536709)
                  ·
                    refine ⟨1872901517330184930475633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9988808092427652962536709 1872901517330184930475633)
                    ·
                      refine ⟨1404676137997638697856725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872901517330184930475633 1404676137997638697856725)
                      ·
                        rfl

theorem cell23_2735597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_2735597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735597 prefixEnd_2735597 := by exact prefixLift 2735597
  have htrace : WordTrace (prefixWord ++ tailWord_2735597) baseStart_2735597 baseEnd_2735597 := by
    simpa [prefixWord, tailWord_2735597, baseEnd_2735597] using wordTrace_append hprefix tailTrace_2735597
  have hstable : (prefixWord ++ tailWord_2735597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735597).length < 2 ^ (prefixWord ++ tailWord_2735597).sum := by decide
  have hdescent : baseEnd_2735597 < baseStart_2735597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735620 : List Nat := [2, 3, 2, 3, 2, 2, 1, 3, 5]
def baseStart_2735620 : Nat := 118140960795 + 2735620 * 2 ^ 59
def prefixEnd_2735620 : Nat := 4983230072969 + 3 ^ 40 * 2735620 * 2
def baseEnd_2735620 : Nat := 156076438672521345318791

theorem tailTrace_2735620 : CollatzResearch.WordTrace tailWord_2735620 prefixEnd_2735620 156076438672521345318791 := by
  unfold tailWord_2735620
  simp only [CollatzResearch.WordTrace]
  refine ⟨49888129174661710772442157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66517505566215614363256209 49888129174661710772442157)
  ·
    refine ⟨18708048440498141539665809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49888129174661710772442157 18708048440498141539665809)
    ·
      refine ⟨14031036330373606154749357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18708048440498141539665809 14031036330373606154749357)
      ·
        refine ⟨5261638623890102308031009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14031036330373606154749357 5261638623890102308031009)
        ·
          refine ⟨3946228967917576731023257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5261638623890102308031009 3946228967917576731023257)
          ·
            refine ⟨2959671725938182548267443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3946228967917576731023257 2959671725938182548267443)
            ·
              refine ⟨4439507588907273822401165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959671725938182548267443 4439507588907273822401165)
              ·
                refine ⟨1664815345840227683400437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4439507588907273822401165 1664815345840227683400437)
                ·
                  refine ⟨156076438672521345318791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1664815345840227683400437 156076438672521345318791)
                  ·
                    rfl

theorem cell23_2735620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_2735620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735620 prefixEnd_2735620 := by exact prefixLift 2735620
  have htrace : WordTrace (prefixWord ++ tailWord_2735620) baseStart_2735620 baseEnd_2735620 := by
    simpa [prefixWord, tailWord_2735620, baseEnd_2735620] using wordTrace_append hprefix tailTrace_2735620
  have hstable : (prefixWord ++ tailWord_2735620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735620).length < 2 ^ (prefixWord ++ tailWord_2735620).sum := by decide
  have hdescent : baseEnd_2735620 < baseStart_2735620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735670 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2735670 : Nat := 118140960795 + 2735670 * 2 ^ 59
def prefixEnd_2735670 : Nat := 4983230072969 + 3 ^ 40 * 2735670 * 2
def baseEnd_2735670 : Nat := 1404713622085416912243889

theorem tailTrace_2735670 : CollatzResearch.WordTrace tailWord_2735670 prefixEnd_2735670 1404713622085416912243889 := by
  unfold tailWord_2735670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6236130124946392505262779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66518721332761520056136309 6236130124946392505262779)
  ·
    refine ⟨9354195187419588757894169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6236130124946392505262779 9354195187419588757894169)
    ·
      refine ⟨7015646390564691568420627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9354195187419588757894169 7015646390564691568420627)
      ·
        refine ⟨10523469585847037352630941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7015646390564691568420627 10523469585847037352630941)
        ·
          refine ⟨3946301094692639007236603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10523469585847037352630941 3946301094692639007236603)
          ·
            refine ⟨5919451642038958510854905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946301094692639007236603 5919451642038958510854905)
            ·
              refine ⟨4439588731529218883141179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919451642038958510854905 4439588731529218883141179)
              ·
                refine ⟨6659383097293828324711769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439588731529218883141179 6659383097293828324711769)
                ·
                  refine ⟨4994537322970371243533827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6659383097293828324711769 4994537322970371243533827)
                  ·
                    refine ⟨7491805984455556865300741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4994537322970371243533827 7491805984455556865300741)
                    ·
                      refine ⟨1404713622085416912243889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7491805984455556865300741 1404713622085416912243889)
                      ·
                        rfl

theorem cell23_2735670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2735670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735670 prefixEnd_2735670 := by exact prefixLift 2735670
  have htrace : WordTrace (prefixWord ++ tailWord_2735670) baseStart_2735670 baseEnd_2735670 := by
    simpa [prefixWord, tailWord_2735670, baseEnd_2735670] using wordTrace_append hprefix tailTrace_2735670
  have hstable : (prefixWord ++ tailWord_2735670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735670).length < 2 ^ (prefixWord ++ tailWord_2735670).sum := by decide
  have hdescent : baseEnd_2735670 < baseStart_2735670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735673 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2735673 : Nat := 118140960795 + 2735673 * 2 ^ 59
def prefixEnd_2735673 : Nat := 4983230072969 + 3 ^ 40 * 2735673 * 2
def baseEnd_2735673 : Nat := 1404715162527380400506375

theorem tailTrace_2735673 : CollatzResearch.WordTrace tailWord_2735673 prefixEnd_2735673 1404715162527380400506375 := by
  unfold tailWord_2735673
  simp only [CollatzResearch.WordTrace]
  refine ⟨99778191418131411596563673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66518794278754274397709115 99778191418131411596563673)
  ·
    refine ⟨74833643563598558697422755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99778191418131411596563673 74833643563598558697422755)
    ·
      refine ⟨112250465345397838046134133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74833643563598558697422755 112250465345397838046134133)
      ·
        refine ⟨10523481126131047316825075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112250465345397838046134133 10523481126131047316825075)
        ·
          refine ⟨15785221689196570975237613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10523481126131047316825075 15785221689196570975237613)
          ·
            refine ⟨5919458133448714115714105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15785221689196570975237613 5919458133448714115714105)
            ·
              refine ⟨4439593600086535586785579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919458133448714115714105 4439593600086535586785579)
              ·
                refine ⟨6659390400129803380178369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439593600086535586785579 6659390400129803380178369)
                ·
                  refine ⟨4994542800097352535133777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6659390400129803380178369 4994542800097352535133777)
                  ·
                    refine ⟨3745907100073014401350333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4994542800097352535133777 3745907100073014401350333)
                    ·
                      refine ⟨1404715162527380400506375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3745907100073014401350333 1404715162527380400506375)
                      ·
                        rfl

theorem cell23_2735673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2735673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735673 prefixEnd_2735673 := by exact prefixLift 2735673
  have htrace : WordTrace (prefixWord ++ tailWord_2735673) baseStart_2735673 baseEnd_2735673 := by
    simpa [prefixWord, tailWord_2735673, baseEnd_2735673] using wordTrace_append hprefix tailTrace_2735673
  have hstable : (prefixWord ++ tailWord_2735673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735673).length < 2 ^ (prefixWord ++ tailWord_2735673).sum := by decide
  have hdescent : baseEnd_2735673 < baseStart_2735673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735720 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2735720 : Nat := 118140960795 + 2735720 * 2 ^ 59
def prefixEnd_2735720 : Nat := 4983230072969 + 3 ^ 40 * 2735720 * 2
def baseEnd_2735720 : Nat := 1404739296118141716618659

theorem tailTrace_2735720 : CollatzResearch.WordTrace tailWord_2735720 prefixEnd_2735720 1404739296118141716618659 := by
  unfold tailWord_2735720
  simp only [CollatzResearch.WordTrace]
  refine ⟨49889952824480569311762307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66519937099307425749016409 49889952824480569311762307)
  ·
    refine ⟨74834929236720853967643461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49889952824480569311762307 74834929236720853967643461)
    ·
      refine ⟨14031549231885160118933149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74834929236720853967643461 14031549231885160118933149)
      ·
        refine ⟨5261830961956935044599931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14031549231885160118933149 5261830961956935044599931)
        ·
          refine ⟨7892746442935402566899897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261830961956935044599931 7892746442935402566899897)
          ·
            refine ⟨5919559832201551925174923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7892746442935402566899897 5919559832201551925174923)
            ·
              refine ⟨8879339748302327887762385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5919559832201551925174923 8879339748302327887762385)
              ·
                refine ⟨6659504811226745915821789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8879339748302327887762385 6659504811226745915821789)
                ·
                  refine ⟨2497314304210029718433171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6659504811226745915821789 2497314304210029718433171)
                  ·
                    refine ⟨3745971456315044577649757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2497314304210029718433171 3745971456315044577649757)
                    ·
                      refine ⟨1404739296118141716618659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3745971456315044577649757 1404739296118141716618659)
                      ·
                        rfl

theorem cell23_2735720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2735720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735720 prefixEnd_2735720 := by exact prefixLift 2735720
  have htrace : WordTrace (prefixWord ++ tailWord_2735720) baseStart_2735720 baseEnd_2735720 := by
    simpa [prefixWord, tailWord_2735720, baseEnd_2735720] using wordTrace_append hprefix tailTrace_2735720
  have hstable : (prefixWord ++ tailWord_2735720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735720).length < 2 ^ (prefixWord ++ tailWord_2735720).sum := by decide
  have hdescent : baseEnd_2735720 < baseStart_2735720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735730 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_2735730 : Nat := 118140960795 + 2735730 * 2 ^ 59
def prefixEnd_2735730 : Nat := 4983230072969 + 3 ^ 40 * 2735730 * 2
def baseEnd_2735730 : Nat := 1404744430924686677493613

theorem tailTrace_2735730 : CollatzResearch.WordTrace tailWord_2735730 prefixEnd_2735730 1404744430924686677493613 := by
  unfold tailWord_2735730
  simp only [CollatzResearch.WordTrace]
  refine ⟨24945067594731227582847161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66520180252616606887592429 24945067594731227582847161)
  ·
    refine ⟨18708800696048420687135371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24945067594731227582847161 18708800696048420687135371)
    ·
      refine ⟨28063201044072631030703057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18708800696048420687135371 28063201044072631030703057)
      ·
        refine ⟨21047400783054473273027293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28063201044072631030703057 21047400783054473273027293)
        ·
          refine ⟨7892775293645427477385235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21047400783054473273027293 7892775293645427477385235)
          ·
            refine ⟨11839162940468141216077853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7892775293645427477385235 11839162940468141216077853)
            ·
              refine ⟨4439686102675552956029195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11839162940468141216077853 4439686102675552956029195)
              ·
                refine ⟨6659529154013329434043793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439686102675552956029195 6659529154013329434043793)
                ·
                  refine ⟨4994646865509997075532845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6659529154013329434043793 4994646865509997075532845)
                  ·
                    refine ⟨1872992574566248903324817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4994646865509997075532845 1872992574566248903324817)
                    ·
                      refine ⟨1404744430924686677493613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1872992574566248903324817 1404744430924686677493613)
                      ·
                        rfl

theorem cell23_2735730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_2735730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735730 prefixEnd_2735730 := by exact prefixLift 2735730
  have htrace : WordTrace (prefixWord ++ tailWord_2735730) baseStart_2735730 baseEnd_2735730 := by
    simpa [prefixWord, tailWord_2735730, baseEnd_2735730] using wordTrace_append hprefix tailTrace_2735730
  have hstable : (prefixWord ++ tailWord_2735730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735730).length < 2 ^ (prefixWord ++ tailWord_2735730).sum := by decide
  have hdescent : baseEnd_2735730 < baseStart_2735730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735749 : List Nat := [1, 3, 1, 1, 4, 1, 12]
def baseStart_2735749 : Nat := 118140960795 + 2735749 * 2 ^ 59
def prefixEnd_2735749 : Nat := 4983230072969 + 3 ^ 40 * 2735749 * 2
def baseEnd_2735749 : Nat := 17342644284655828434025

theorem tailTrace_2735749 : CollatzResearch.WordTrace tailWord_2735749 prefixEnd_2735749 17342644284655828434025 := by
  unfold tailWord_2735749
  simp only [CollatzResearch.WordTrace]
  refine ⟨99780963365856076576330301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66520642243904051050886867 99780963365856076576330301)
  ·
    refine ⟨37417861262196028716123863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99780963365856076576330301 37417861262196028716123863)
    ·
      refine ⟨56126791893294043074185795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37417861262196028716123863 56126791893294043074185795)
      ·
        refine ⟨84190187839941064611278693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56126791893294043074185795 84190187839941064611278693)
        ·
          refine ⟨15785660219988949614614755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84190187839941064611278693 15785660219988949614614755)
          ·
            refine ⟨23678490329983424421922133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15785660219988949614614755 23678490329983424421922133)
            ·
              refine ⟨17342644284655828434025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 23678490329983424421922133 17342644284655828434025)
              ·
                rfl

theorem cell23_2735749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 12].length) (baseStart_2735749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735749 prefixEnd_2735749 := by exact prefixLift 2735749
  have htrace : WordTrace (prefixWord ++ tailWord_2735749) baseStart_2735749 baseEnd_2735749 := by
    simpa [prefixWord, tailWord_2735749, baseEnd_2735749] using wordTrace_append hprefix tailTrace_2735749
  have hstable : (prefixWord ++ tailWord_2735749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735749).length < 2 ^ (prefixWord ++ tailWord_2735749).sum := by decide
  have hdescent : baseEnd_2735749 < baseStart_2735749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735753 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 2, 4]
def baseStart_2735753 : Nat := 118140960795 + 2735753 * 2 ^ 59
def prefixEnd_2735753 : Nat := 4983230072969 + 3 ^ 40 * 2735753 * 2
def baseEnd_2735753 : Nat := 468252080326580029168669

theorem tailTrace_2735753 : CollatzResearch.WordTrace tailWord_2735753 prefixEnd_2735753 468252080326580029168669 := by
  unfold tailWord_2735753
  simp only [CollatzResearch.WordTrace]
  refine ⟨99781109257841585259475913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66520739505227723506317275 99781109257841585259475913)
  ·
    refine ⟨74835831943381188944606935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99781109257841585259475913 74835831943381188944606935)
    ·
      refine ⟨112253747915071783416910403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74835831943381188944606935 112253747915071783416910403)
      ·
        refine ⟨168380621872607675125365605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112253747915071783416910403 168380621872607675125365605)
        ·
          refine ⟨31571366601113939086006051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168380621872607675125365605 31571366601113939086006051)
          ·
            refine ⟨47357049901670908629009077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31571366601113939086006051 47357049901670908629009077)
            ·
              refine ⟨4439723428281647683969601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47357049901670908629009077 4439723428281647683969601)
              ·
                refine ⟨3329792571211235762977201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4439723428281647683969601 3329792571211235762977201)
                ·
                  refine ⟨2497344428408426822232901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3329792571211235762977201 2497344428408426822232901)
                  ·
                    refine ⟨468252080326580029168669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2497344428408426822232901 468252080326580029168669)
                    ·
                      rfl

theorem cell23_2735753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 4].length) (baseStart_2735753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735753 prefixEnd_2735753 := by exact prefixLift 2735753
  have htrace : WordTrace (prefixWord ++ tailWord_2735753) baseStart_2735753 baseEnd_2735753 := by
    simpa [prefixWord, tailWord_2735753, baseEnd_2735753] using wordTrace_append hprefix tailTrace_2735753
  have hstable : (prefixWord ++ tailWord_2735753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735753).length < 2 ^ (prefixWord ++ tailWord_2735753).sum := by decide
  have hdescent : baseEnd_2735753 < baseStart_2735753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735769 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2735769 : Nat := 118140960795 + 2735769 * 2 ^ 59
def prefixEnd_2735769 : Nat := 4983230072969 + 3 ^ 40 * 2735769 * 2
def baseEnd_2735769 : Nat := 1404764456670212024905933

theorem tailTrace_2735769 : CollatzResearch.WordTrace tailWord_2735769 prefixEnd_2735769 1404764456670212024905933 := by
  unfold tailWord_2735769
  simp only [CollatzResearch.WordTrace]
  refine ⟨99781692825783619992058361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66521128550522413328038907 99781692825783619992058361)
  ·
    refine ⟨74836269619337714994043771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99781692825783619992058361 74836269619337714994043771)
    ·
      refine ⟨112254404429006572491065657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74836269619337714994043771 112254404429006572491065657)
      ·
        refine ⟨84190803321754929368299243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112254404429006572491065657 84190803321754929368299243)
        ·
          refine ⟨126286204982632394052448865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84190803321754929368299243 126286204982632394052448865)
          ·
            refine ⟨94714653736974295539336649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126286204982632394052448865 94714653736974295539336649)
            ·
              refine ⟨71035990302730721654502487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94714653736974295539336649 71035990302730721654502487)
              ·
                refine ⟨106553985454096082481753731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71035990302730721654502487 106553985454096082481753731)
                ·
                  refine ⟨159830978181144123722630597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106553985454096082481753731 159830978181144123722630597)
                  ·
                    refine ⟨29968308408964523197993237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159830978181144123722630597 29968308408964523197993237)
                    ·
                      refine ⟨1404764456670212024905933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29968308408964523197993237 1404764456670212024905933)
                      ·
                        rfl

theorem cell23_2735769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2735769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735769 prefixEnd_2735769 := by exact prefixLift 2735769
  have htrace : WordTrace (prefixWord ++ tailWord_2735769) baseStart_2735769 baseEnd_2735769 := by
    simpa [prefixWord, tailWord_2735769, baseEnd_2735769] using wordTrace_append hprefix tailTrace_2735769
  have hstable : (prefixWord ++ tailWord_2735769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735769).length < 2 ^ (prefixWord ++ tailWord_2735769).sum := by decide
  have hdescent : baseEnd_2735769 < baseStart_2735769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735780 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_2735780 : Nat := 118140960795 + 2735780 * 2 ^ 59
def prefixEnd_2735780 : Nat := 4983230072969 + 3 ^ 40 * 2735780 * 2
def baseEnd_2735780 : Nat := 1404770104957411481868383

theorem tailTrace_2735780 : CollatzResearch.WordTrace tailWord_2735780 prefixEnd_2735780 1404770104957411481868383 := by
  unfold tailWord_2735780
  simp only [CollatzResearch.WordTrace]
  refine ⟨49891047014371884435354397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66521396019162512580472529 49891047014371884435354397)
  ·
    refine ⟨18709142630389456663257899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49891047014371884435354397 18709142630389456663257899)
    ·
      refine ⟨28063713945584184994886849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18709142630389456663257899 28063713945584184994886849)
      ·
        refine ⟨21047785459188138746165137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28063713945584184994886849 21047785459188138746165137)
        ·
          refine ⟨15785839094391104059623853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21047785459188138746165137 15785839094391104059623853)
          ·
            refine ⟨5919689660396664022358945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15785839094391104059623853 5919689660396664022358945)
            ·
              refine ⟨4439767245297498016769209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919689660396664022358945 4439767245297498016769209)
              ·
                refine ⟨3329825433973123512576907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4439767245297498016769209 3329825433973123512576907)
                ·
                  refine ⟨4994738150959685268865361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329825433973123512576907 4994738150959685268865361)
                  ·
                    refine ⟨3746053613219763951649021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4994738150959685268865361 3746053613219763951649021)
                    ·
                      refine ⟨1404770104957411481868383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3746053613219763951649021 1404770104957411481868383)
                      ·
                        rfl

theorem cell23_2735780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_2735780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735780 prefixEnd_2735780 := by exact prefixLift 2735780
  have htrace : WordTrace (prefixWord ++ tailWord_2735780) baseStart_2735780 baseEnd_2735780 := by
    simpa [prefixWord, tailWord_2735780, baseEnd_2735780] using wordTrace_append hprefix tailTrace_2735780
  have hstable : (prefixWord ++ tailWord_2735780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735780).length < 2 ^ (prefixWord ++ tailWord_2735780).sum := by decide
  have hdescent : baseEnd_2735780 < baseStart_2735780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735816 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2735816 : Nat := 118140960795 + 2735816 * 2 ^ 59
def prefixEnd_2735816 : Nat := 4983230072969 + 3 ^ 40 * 2735816 * 2
def baseEnd_2735816 : Nat := 1404788590260973341018217

theorem tailTrace_2735816 : CollatzResearch.WordTrace tailWord_2735816 prefixEnd_2735816 1404788590260973341018217 := by
  unfold tailWord_2735816
  simp only [CollatzResearch.WordTrace]
  refine ⟨49891703528306673509509651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66522271371075564679346201 49891703528306673509509651)
  ·
    refine ⟨74837555292460010264264477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49891703528306673509509651 74837555292460010264264477)
    ·
      refine ⟨28064083234672503849099179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74837555292460010264264477 28064083234672503849099179)
      ·
        refine ⟨42096124852008755773648769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28064083234672503849099179 42096124852008755773648769)
        ·
          refine ⟨31572093639006566830236577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42096124852008755773648769 31572093639006566830236577)
          ·
            refine ⟨23679070229254925122677433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31572093639006566830236577 23679070229254925122677433)
            ·
              refine ⟨17759302671941193842008075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23679070229254925122677433 17759302671941193842008075)
              ·
                refine ⟨26638954007911790763012113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17759302671941193842008075 26638954007911790763012113)
                ·
                  refine ⟨19979215505933843072259085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26638954007911790763012113 19979215505933843072259085)
                  ·
                    refine ⟨7492205814725191152097157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19979215505933843072259085 7492205814725191152097157)
                    ·
                      refine ⟨1404788590260973341018217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7492205814725191152097157 1404788590260973341018217)
                      ·
                        rfl

theorem cell23_2735816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2735816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735816 prefixEnd_2735816 := by exact prefixLift 2735816
  have htrace : WordTrace (prefixWord ++ tailWord_2735816) baseStart_2735816 baseEnd_2735816 := by
    simpa [prefixWord, tailWord_2735816, baseEnd_2735816] using wordTrace_append hprefix tailTrace_2735816
  have hstable : (prefixWord ++ tailWord_2735816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735816).length < 2 ^ (prefixWord ++ tailWord_2735816).sum := by decide
  have hdescent : baseEnd_2735816 < baseStart_2735816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735850 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_2735850 : Nat := 118140960795 + 2735850 * 2 ^ 59
def prefixEnd_2735850 : Nat := 4983230072969 + 3 ^ 40 * 2735850 * 2
def baseEnd_2735850 : Nat := 1404806048603226207993061

theorem tailTrace_2735850 : CollatzResearch.WordTrace tailWord_2735850 prefixEnd_2735850 1404806048603226207993061 := by
  unfold tailWord_2735850
  simp only [CollatzResearch.WordTrace]
  refine ⟨24946161784622542706439251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66523098092326780550504669 24946161784622542706439251)
  ·
    refine ⟨37419242676933814059658877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24946161784622542706439251 37419242676933814059658877)
    ·
      refine ⟨14032216003850180272372079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37419242676933814059658877 14032216003850180272372079)
      ·
        refine ⟨21048324005775270408558119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14032216003850180272372079 21048324005775270408558119)
        ·
          refine ⟨31572486008662905612837179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21048324005775270408558119 31572486008662905612837179)
          ·
            refine ⟨47358729012994358419255769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31572486008662905612837179 47358729012994358419255769)
            ·
              refine ⟨35519046759745768814441827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47358729012994358419255769 35519046759745768814441827)
              ·
                refine ⟨53278570139618653221662741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35519046759745768814441827 53278570139618653221662741)
                ·
                  refine ⟨2497432975294624369765441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53278570139618653221662741 2497432975294624369765441)
                  ·
                    refine ⟨1873074731470968277324081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2497432975294624369765441 1873074731470968277324081)
                    ·
                      refine ⟨1404806048603226207993061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873074731470968277324081 1404806048603226207993061)
                      ·
                        rfl

theorem cell23_2735850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_2735850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735850 prefixEnd_2735850 := by exact prefixLift 2735850
  have htrace : WordTrace (prefixWord ++ tailWord_2735850) baseStart_2735850 baseEnd_2735850 := by
    simpa [prefixWord, tailWord_2735850, baseEnd_2735850] using wordTrace_append hprefix tailTrace_2735850
  have hstable : (prefixWord ++ tailWord_2735850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735850).length < 2 ^ (prefixWord ++ tailWord_2735850).sum := by decide
  have hdescent : baseEnd_2735850 < baseStart_2735850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735853 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2735853 : Nat := 118140960795 + 2735853 * 2 ^ 59
def prefixEnd_2735853 : Nat := 4983230072969 + 3 ^ 40 * 2735853 * 2
def baseEnd_2735853 : Nat := 1404807589045189696255547

theorem tailTrace_2735853 : CollatzResearch.WordTrace tailWord_2735853 prefixEnd_2735853 1404807589045189696255547 := by
  unfold tailWord_2735853
  simp only [CollatzResearch.WordTrace]
  refine ⟨99784756557479302338116213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66523171038319534892077475 99784756557479302338116213)
  ·
    refine ⟨9354820927263684594198395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99784756557479302338116213 9354820927263684594198395)
    ·
      refine ⟨14032231390895526891297593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9354820927263684594198395 14032231390895526891297593)
      ·
        refine ⟨10524173543171645168473195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14032231390895526891297593 10524173543171645168473195)
        ·
          refine ⟨15786260314757467752709793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10524173543171645168473195 15786260314757467752709793)
          ·
            refine ⟨11839695236068100814532345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15786260314757467752709793 11839695236068100814532345)
            ·
              refine ⟨8879771427051075610899259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11839695236068100814532345 8879771427051075610899259)
              ·
                refine ⟨13319657140576613416348889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8879771427051075610899259 13319657140576613416348889)
                ·
                  refine ⟨9989742855432460062261667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13319657140576613416348889 9989742855432460062261667)
                  ·
                    refine ⟨14984614283148690093392501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9989742855432460062261667 14984614283148690093392501)
                    ·
                      refine ⟨1404807589045189696255547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14984614283148690093392501 1404807589045189696255547)
                      ·
                        rfl

theorem cell23_2735853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2735853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735853 prefixEnd_2735853 := by exact prefixLift 2735853
  have htrace : WordTrace (prefixWord ++ tailWord_2735853) baseStart_2735853 baseEnd_2735853 := by
    simpa [prefixWord, tailWord_2735853, baseEnd_2735853] using wordTrace_append hprefix tailTrace_2735853
  have hstable : (prefixWord ++ tailWord_2735853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735853).length < 2 ^ (prefixWord ++ tailWord_2735853).sum := by decide
  have hdescent : baseEnd_2735853 < baseStart_2735853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735878 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2735878 : Nat := 118140960795 + 2735878 * 2 ^ 59
def prefixEnd_2735878 : Nat := 4983230072969 + 3 ^ 40 * 2735878 * 2
def baseEnd_2735878 : Nat := 1404820426061552098442933

theorem tailTrace_2735878 : CollatzResearch.WordTrace tailWord_2735878 prefixEnd_2735878 1404820426061552098442933 := by
  unfold tailWord_2735878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118302136949647862743009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66523778921592487738517525 3118302136949647862743009)
  ·
    refine ⟨2338726602712235897057257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3118302136949647862743009 2338726602712235897057257)
    ·
      refine ⟨1754044952034176922792943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2338726602712235897057257 1754044952034176922792943)
      ·
        refine ⟨2631067428051265384189415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1754044952034176922792943 2631067428051265384189415)
        ·
          refine ⟨3946601142076898076284123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2631067428051265384189415 3946601142076898076284123)
          ·
            refine ⟨5919901713115347114426185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946601142076898076284123 5919901713115347114426185)
            ·
              refine ⟨4439926284836510335819639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5919901713115347114426185 4439926284836510335819639)
              ·
                refine ⟨6659889427254765503729459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439926284836510335819639 6659889427254765503729459)
                ·
                  refine ⟨9989834140882148255594189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6659889427254765503729459 9989834140882148255594189)
                  ·
                    refine ⟨3746187802830805595847821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9989834140882148255594189 3746187802830805595847821)
                    ·
                      refine ⟨1404820426061552098442933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3746187802830805595847821 1404820426061552098442933)
                      ·
                        rfl

theorem cell23_2735878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2735878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735878 prefixEnd_2735878 := by exact prefixLift 2735878
  have htrace : WordTrace (prefixWord ++ tailWord_2735878) baseStart_2735878 baseEnd_2735878 := by
    simpa [prefixWord, tailWord_2735878, baseEnd_2735878] using wordTrace_append hprefix tailTrace_2735878
  have hstable : (prefixWord ++ tailWord_2735878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735878).length < 2 ^ (prefixWord ++ tailWord_2735878).sum := by decide
  have hdescent : baseEnd_2735878 < baseStart_2735878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735890 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 7]
def baseStart_2735890 : Nat := 118140960795 + 2735890 * 2 ^ 59
def prefixEnd_2735890 : Nat := 4983230072969 + 3 ^ 40 * 2735890 * 2
def baseEnd_2735890 : Nat := 156091843092156227943653

theorem tailTrace_2735890 : CollatzResearch.WordTrace tailWord_2735890 prefixEnd_2735890 156091843092156227943653 := by
  unfold tailWord_2735890
  simp only [CollatzResearch.WordTrace]
  refine ⟨24946526514586314414303281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66524070705563505104808749 24946526514586314414303281)
  ·
    refine ⟨18709894885939735810727461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24946526514586314414303281 18709894885939735810727461)
    ·
      refine ⟨3508105291113700464511399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18709894885939735810727461 3508105291113700464511399)
      ·
        refine ⟨5262157936670550696767099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3508105291113700464511399 5262157936670550696767099)
        ·
          refine ⟨7893236905005826045150649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5262157936670550696767099 7893236905005826045150649)
          ·
            refine ⟨5919927678754369533862987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7893236905005826045150649 5919927678754369533862987)
            ·
              refine ⟨8879891518131554300794481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5919927678754369533862987 8879891518131554300794481)
              ·
                refine ⟨6659918638598665725595861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8879891518131554300794481 6659918638598665725595861)
                ·
                  refine ⟨156091843092156227943653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6659918638598665725595861 156091843092156227943653)
                  ·
                    rfl

theorem cell23_2735890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_2735890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735890 prefixEnd_2735890 := by exact prefixLift 2735890
  have htrace : WordTrace (prefixWord ++ tailWord_2735890) baseStart_2735890 baseEnd_2735890 := by
    simpa [prefixWord, tailWord_2735890, baseEnd_2735890] using wordTrace_append hprefix tailTrace_2735890
  have hstable : (prefixWord ++ tailWord_2735890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735890).length < 2 ^ (prefixWord ++ tailWord_2735890).sum := by decide
  have hdescent : baseEnd_2735890 < baseStart_2735890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735896 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2735896 : Nat := 118140960795 + 2735896 * 2 ^ 59
def prefixEnd_2735896 : Nat := 4983230072969 + 3 ^ 40 * 2735896 * 2
def baseEnd_2735896 : Nat := 1404829668713333028017849

theorem tailTrace_2735896 : CollatzResearch.WordTrace tailWord_2735896 prefixEnd_2735896 1404829668713333028017849 := by
  unfold tailWord_2735896
  simp only [CollatzResearch.WordTrace]
  refine ⟨49893162448161760340965771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66524216597549013787954361 49893162448161760340965771)
  ·
    refine ⟨74839743672242640511448657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49893162448161760340965771 74839743672242640511448657)
    ·
      refine ⟨56129807754181980383586493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74839743672242640511448657 56129807754181980383586493)
      ·
        refine ⟨21048677907818242643844935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56129807754181980383586493 21048677907818242643844935)
        ·
          refine ⟨31573016861727363965767403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21048677907818242643844935 31573016861727363965767403)
          ·
            refine ⟨47359525292591045948651105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31573016861727363965767403 47359525292591045948651105)
            ·
              refine ⟨35519643969443284461488329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47359525292591045948651105 35519643969443284461488329)
              ·
                refine ⟨26639732977082463346116247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35519643969443284461488329 26639732977082463346116247)
                ·
                  refine ⟨39959599465623695019174371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26639732977082463346116247 39959599465623695019174371)
                  ·
                    refine ⟨59939399198435542528761557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39959599465623695019174371 59939399198435542528761557)
                    ·
                      refine ⟨1404829668713333028017849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59939399198435542528761557 1404829668713333028017849)
                      ·
                        rfl

theorem cell23_2735896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2735896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735896 prefixEnd_2735896 := by exact prefixLift 2735896
  have htrace : WordTrace (prefixWord ++ tailWord_2735896) baseStart_2735896 baseEnd_2735896 := by
    simpa [prefixWord, tailWord_2735896, baseEnd_2735896] using wordTrace_append hprefix tailTrace_2735896
  have hstable : (prefixWord ++ tailWord_2735896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735896).length < 2 ^ (prefixWord ++ tailWord_2735896).sum := by decide
  have hdescent : baseEnd_2735896 < baseStart_2735896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735918 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_2735918 : Nat := 118140960795 + 2735918 * 2 ^ 59
def prefixEnd_2735918 : Nat := 4983230072969 + 3 ^ 40 * 2735918 * 2
def baseEnd_2735918 : Nat := 1404840965287731941942749

theorem tailTrace_2735918 : CollatzResearch.WordTrace tailWord_2735918 prefixEnd_2735918 1404840965287731941942749 := by
  unfold tailWord_2735918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12473390912780477304904051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66524751534829212292821605 12473390912780477304904051)
  ·
    refine ⟨18710086369170715957356077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12473390912780477304904051 18710086369170715957356077)
    ·
      refine ⟨7016282388439018484008529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18710086369170715957356077 7016282388439018484008529)
      ·
        refine ⟨5262211791329263863006397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7016282388439018484008529 5262211791329263863006397)
        ·
          refine ⟨1973329421748473948627399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5262211791329263863006397 1973329421748473948627399)
          ·
            refine ⟨2959994132622710922941099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973329421748473948627399 2959994132622710922941099)
            ·
              refine ⟨4439991198934066384411649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959994132622710922941099 4439991198934066384411649)
              ·
                refine ⟨3329993399200549788308737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4439991198934066384411649 3329993399200549788308737)
                ·
                  refine ⟨2497495049400412341231553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3329993399200549788308737 2497495049400412341231553)
                  ·
                    refine ⟨1873121287050309255923665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2497495049400412341231553 1873121287050309255923665)
                    ·
                      refine ⟨1404840965287731941942749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873121287050309255923665 1404840965287731941942749)
                      ·
                        rfl

theorem cell23_2735918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_2735918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735918 prefixEnd_2735918 := by exact prefixLift 2735918
  have htrace : WordTrace (prefixWord ++ tailWord_2735918) baseStart_2735918 baseEnd_2735918 := by
    simpa [prefixWord, tailWord_2735918, baseEnd_2735918] using wordTrace_append hprefix tailTrace_2735918
  have hstable : (prefixWord ++ tailWord_2735918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735918).length < 2 ^ (prefixWord ++ tailWord_2735918).sum := by decide
  have hdescent : baseEnd_2735918 < baseStart_2735918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735943 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_2735943 : Nat := 118140960795 + 2735943 * 2 ^ 59
def prefixEnd_2735943 : Nat := 4983230072969 + 3 ^ 40 * 2735943 * 2
def baseEnd_2735943 : Nat := 1404853802304094344130133

theorem tailTrace_2735943 : CollatzResearch.WordTrace tailWord_2735943 prefixEnd_2735943 1404853802304094344130133 := by
  unfold tailWord_2735943
  simp only [CollatzResearch.WordTrace]
  refine ⟨99788039127153247708892483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66525359418102165139261655 99788039127153247708892483)
  ·
    refine ⟨149682058690729871563338725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99788039127153247708892483 149682058690729871563338725)
    ·
      refine ⟨28065386004511850918126011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149682058690729871563338725 28065386004511850918126011)
      ·
        refine ⟨42098079006767776377189017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28065386004511850918126011 42098079006767776377189017)
        ·
          refine ⟨31573559255075832282891763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42098079006767776377189017 31573559255075832282891763)
          ·
            refine ⟨47360338882613748424337645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31573559255075832282891763 47360338882613748424337645)
            ·
              refine ⟨17760127080980155659126617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47360338882613748424337645 17760127080980155659126617)
              ·
                refine ⟨13320095310735116744344963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17760127080980155659126617 13320095310735116744344963)
                ·
                  refine ⟨19980142966102675116517445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13320095310735116744344963 19980142966102675116517445)
                  ·
                    refine ⟨3746276806144251584347021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19980142966102675116517445 3746276806144251584347021)
                    ·
                      refine ⟨1404853802304094344130133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3746276806144251584347021 1404853802304094344130133)
                      ·
                        rfl

theorem cell23_2735943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_2735943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735943 prefixEnd_2735943 := by exact prefixLift 2735943
  have htrace : WordTrace (prefixWord ++ tailWord_2735943) baseStart_2735943 baseEnd_2735943 := by
    simpa [prefixWord, tailWord_2735943, baseEnd_2735943] using wordTrace_append hprefix tailTrace_2735943
  have hstable : (prefixWord ++ tailWord_2735943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735943).length < 2 ^ (prefixWord ++ tailWord_2735943).sum := by decide
  have hdescent : baseEnd_2735943 < baseStart_2735943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735967 : List Nat := [1, 1, 2, 3, 1, 4, 3, 3, 1, 4]
def baseStart_2735967 : Nat := 118140960795 + 2735967 * 2 ^ 59
def prefixEnd_2735967 : Nat := 4983230072969 + 3 ^ 40 * 2735967 * 2
def baseEnd_2735967 : Nat := 468288708613267416743341

theorem tailTrace_2735967 : CollatzResearch.WordTrace tailWord_2735967 prefixEnd_2735967 468288708613267416743341 := by
  unfold tailWord_2735967
  simp only [CollatzResearch.WordTrace]
  refine ⟨99788914479066299807766155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66525942986044199871844103 99788914479066299807766155)
  ·
    refine ⟨149683371718599449711649233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99788914479066299807766155 149683371718599449711649233)
    ·
      refine ⟨112262528788949587283736925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149683371718599449711649233 112262528788949587283736925)
      ·
        refine ⟨42098448295856095231401347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112262528788949587283736925 42098448295856095231401347)
        ·
          refine ⟨63147672443784142847102021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42098448295856095231401347 63147672443784142847102021)
          ·
            refine ⟨11840188583209526783831629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63147672443784142847102021 11840188583209526783831629)
            ·
              refine ⟨4440070718703572543936861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11840188583209526783831629 4440070718703572543936861)
              ·
                refine ⟨1665026519513839703976323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4440070718703572543936861 1665026519513839703976323)
                ·
                  refine ⟨2497539779270759555964485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665026519513839703976323 2497539779270759555964485)
                  ·
                    refine ⟨468288708613267416743341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2497539779270759555964485 468288708613267416743341)
                    ·
                      rfl

theorem cell23_2735967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 4].length) (baseStart_2735967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735967 prefixEnd_2735967 := by exact prefixLift 2735967
  have htrace : WordTrace (prefixWord ++ tailWord_2735967) baseStart_2735967 baseEnd_2735967 := by
    simpa [prefixWord, tailWord_2735967, baseEnd_2735967] using wordTrace_append hprefix tailTrace_2735967
  have hstable : (prefixWord ++ tailWord_2735967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735967).length < 2 ^ (prefixWord ++ tailWord_2735967).sum := by decide
  have hdescent : baseEnd_2735967 < baseStart_2735967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2735993 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 3, 5]
def baseStart_2735993 : Nat := 118140960795 + 2735993 * 2 ^ 59
def prefixEnd_2735993 : Nat := 4983230072969 + 3 ^ 40 * 2735993 * 2
def baseEnd_2735993 : Nat := 468293158778939716168301

theorem tailTrace_2735993 : CollatzResearch.WordTrace tailWord_2735993 prefixEnd_2735993 468293158778939716168301 := by
  unfold tailWord_2735993
  simp only [CollatzResearch.WordTrace]
  refine ⟨99789862776972106248212633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66526575184648070832141755 99789862776972106248212633)
  ·
    refine ⟨74842397082729079686159475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99789862776972106248212633 74842397082729079686159475)
    ·
      refine ⟨112263595624093619529239213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74842397082729079686159475 112263595624093619529239213)
      ·
        refine ⟨42098848359035107323464705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112263595624093619529239213 42098848359035107323464705)
        ·
          refine ⟨31574136269276330492598529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42098848359035107323464705 31574136269276330492598529)
          ·
            refine ⟨23680602201957247869448897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31574136269276330492598529 23680602201957247869448897)
            ·
              refine ⟨17760451651467935902086673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23680602201957247869448897 17760451651467935902086673)
              ·
                refine ⟨13320338738600951926565005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17760451651467935902086673 13320338738600951926565005)
                ·
                  refine ⟨4995127026975356972461877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13320338738600951926565005 4995127026975356972461877)
                  ·
                    refine ⟨468293158778939716168301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4995127026975356972461877 468293158778939716168301)
                    ·
                      rfl

theorem cell23_2735993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_2735993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2735993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2735993 prefixEnd_2735993 := by exact prefixLift 2735993
  have htrace : WordTrace (prefixWord ++ tailWord_2735993) baseStart_2735993 baseEnd_2735993 := by
    simpa [prefixWord, tailWord_2735993, baseEnd_2735993] using wordTrace_append hprefix tailTrace_2735993
  have hstable : (prefixWord ++ tailWord_2735993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2735993).length < 2 ^ (prefixWord ++ tailWord_2735993).sum := by decide
  have hdescent : baseEnd_2735993 < baseStart_2735993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2735993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736000 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 4, 3, 2]
def baseStart_2736000 : Nat := 118140960795 + 2736000 * 2 ^ 59
def prefixEnd_2736000 : Nat := 4983230072969 + 3 ^ 40 * 2736000 * 2
def baseEnd_2736000 : Nat := 1404883070701400621117371

theorem tailTrace_2736000 : CollatzResearch.WordTrace tailWord_2736000 prefixEnd_2736000 1404883070701400621117371 := by
  unfold tailWord_2736000
  simp only [CollatzResearch.WordTrace]
  refine ⟨49895059043973373221858727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66526745391964497629144969 49895059043973373221858727)
  ·
    refine ⟨74842588565960059832788091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49895059043973373221858727 74842588565960059832788091)
    ·
      refine ⟨112263882848940089749182137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74842588565960059832788091 112263882848940089749182137)
      ·
        refine ⟨84197912136705067311886603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112263882848940089749182137 84197912136705067311886603)
        ·
          refine ⟨126296868205057600967829905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84197912136705067311886603 126296868205057600967829905)
          ·
            refine ⟨94722651153793200725872429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126296868205057600967829905 94722651153793200725872429)
            ·
              refine ⟨35520994182672450272202161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94722651153793200725872429 35520994182672450272202161)
              ·
                refine ⟨26640745637004337704151621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35520994182672450272202161 26640745637004337704151621)
                ·
                  refine ⟨4995139806938313319528429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26640745637004337704151621 4995139806938313319528429)
                  ·
                    refine ⟨1873177427601867494823161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4995139806938313319528429 1873177427601867494823161)
                    ·
                      refine ⟨1404883070701400621117371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873177427601867494823161 1404883070701400621117371)
                      ·
                        rfl

theorem cell23_2736000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_2736000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736000 prefixEnd_2736000 := by exact prefixLift 2736000
  have htrace : WordTrace (prefixWord ++ tailWord_2736000) baseStart_2736000 baseEnd_2736000 := by
    simpa [prefixWord, tailWord_2736000, baseEnd_2736000] using wordTrace_append hprefix tailTrace_2736000
  have hstable : (prefixWord ++ tailWord_2736000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736000).length < 2 ^ (prefixWord ++ tailWord_2736000).sum := by decide
  have hdescent : baseEnd_2736000 < baseStart_2736000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736023 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 3, 6]
def baseStart_2736023 : Nat := 118140960795 + 2736023 * 2 ^ 59
def prefixEnd_2736023 : Nat := 4983230072969 + 3 ^ 40 * 2736023 * 2
def baseEnd_2736023 : Nat := 468298293585484677043255

theorem tailTrace_2736023 : CollatzResearch.WordTrace tailWord_2736023 prefixEnd_2736023 468298293585484677043255 := by
  unfold tailWord_2736023
  simp only [CollatzResearch.WordTrace]
  refine ⟨99790956966863421371804723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66527304644575614247869815 99790956966863421371804723)
  ·
    refine ⟨149686435450295132057707085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99790956966863421371804723 149686435450295132057707085)
    ·
      refine ⟨56132413293860674521640157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149686435450295132057707085 56132413293860674521640157)
      ·
        refine ⟨21049654985197752945615059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56132413293860674521640157 21049654985197752945615059)
        ·
          refine ⟨31574482477796629418422589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21049654985197752945615059 31574482477796629418422589)
          ·
            refine ⟨11840430929173736031908471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31574482477796629418422589 11840430929173736031908471)
            ·
              refine ⟨17760646393760604047862707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11840430929173736031908471 17760646393760604047862707)
              ·
                refine ⟨26640969590640906071794061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17760646393760604047862707 26640969590640906071794061)
                ·
                  refine ⟨9990363596490339776922773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26640969590640906071794061 9990363596490339776922773)
                  ·
                    refine ⟨468298293585484677043255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9990363596490339776922773 468298293585484677043255)
                    ·
                      rfl

theorem cell23_2736023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_2736023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736023 prefixEnd_2736023 := by exact prefixLift 2736023
  have htrace : WordTrace (prefixWord ++ tailWord_2736023) baseStart_2736023 baseEnd_2736023 := by
    simpa [prefixWord, tailWord_2736023, baseEnd_2736023] using wordTrace_append hprefix tailTrace_2736023
  have hstable : (prefixWord ++ tailWord_2736023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736023).length < 2 ^ (prefixWord ++ tailWord_2736023).sum := by decide
  have hdescent : baseEnd_2736023 < baseStart_2736023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736047 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 3, 2, 2]
def baseStart_2736047 : Nat := 118140960795 + 2736047 * 2 ^ 59
def prefixEnd_2736047 : Nat := 4983230072969 + 3 ^ 40 * 2736047 * 2
def baseEnd_2736047 : Nat := 1404907204292161937229655

theorem tailTrace_2736047 : CollatzResearch.WordTrace tailWord_2736047 prefixEnd_2736047 1404907204292161937229655 := by
  unfold tailWord_2736047
  simp only [CollatzResearch.WordTrace]
  refine ⟨99791832318776473470678395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66527888212517648980452263 99791832318776473470678395)
  ·
    refine ⟨149687748478164710206017593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99791832318776473470678395 149687748478164710206017593)
    ·
      refine ⟨112265811358623532654513195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149687748478164710206017593 112265811358623532654513195)
      ·
        refine ⟨168398717037935298981769793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112265811358623532654513195 168398717037935298981769793)
        ·
          refine ⟨126299037778451474236327345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168398717037935298981769793 126299037778451474236327345)
          ·
            refine ⟨94724278333838605677245509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126299037778451474236327345 94724278333838605677245509)
            ·
              refine ⟨17760802187594738564483533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94724278333838605677245509 17760802187594738564483533)
              ·
                refine ⟨6660300820348026961681325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17760802187594738564483533 6660300820348026961681325)
                ·
                  refine ⟨2497612807630510110630497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6660300820348026961681325 2497612807630510110630497)
                  ·
                    refine ⟨1873209605722882582972873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2497612807630510110630497 1873209605722882582972873)
                    ·
                      refine ⟨1404907204292161937229655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873209605722882582972873 1404907204292161937229655)
                      ·
                        rfl

theorem cell23_2736047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 2, 2].length) (baseStart_2736047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736047 prefixEnd_2736047 := by exact prefixLift 2736047
  have htrace : WordTrace (prefixWord ++ tailWord_2736047) baseStart_2736047 baseEnd_2736047 := by
    simpa [prefixWord, tailWord_2736047, baseEnd_2736047] using wordTrace_append hprefix tailTrace_2736047
  have hstable : (prefixWord ++ tailWord_2736047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736047).length < 2 ^ (prefixWord ++ tailWord_2736047).sum := by decide
  have hdescent : baseEnd_2736047 < baseStart_2736047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736080 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 3]
def baseStart_2736080 : Nat := 118140960795 + 2736080 * 2 ^ 59
def prefixEnd_2736080 : Nat := 4983230072969 + 3 ^ 40 * 2736080 * 2
def baseEnd_2736080 : Nat := 1404924149153760308117003

theorem tailTrace_2736080 : CollatzResearch.WordTrace tailWord_2736080 prefixEnd_2736080 1404924149153760308117003 := by
  unfold tailWord_2736080
  simp only [CollatzResearch.WordTrace]
  refine ⟨49896517963828460053314847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66528690618437946737753129 49896517963828460053314847)
  ·
    refine ⟨74844776945742690079972271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49896517963828460053314847 74844776945742690079972271)
    ·
      refine ⟨112267165418614035119958407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74844776945742690079972271 112267165418614035119958407)
      ·
        refine ⟨168400748127921052679937611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112267165418614035119958407 168400748127921052679937611)
        ·
          refine ⟨252601122191881579019906417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168400748127921052679937611 252601122191881579019906417)
          ·
            refine ⟨189450841643911184264929813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252601122191881579019906417 189450841643911184264929813)
            ·
              refine ⟨8880508202058336762418585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189450841643911184264929813 8880508202058336762418585)
              ·
                refine ⟨6660381151543752571813939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8880508202058336762418585 6660381151543752571813939)
                ·
                  refine ⟨9990571727315628857720909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6660381151543752571813939 9990571727315628857720909)
                  ·
                    refine ⟨3746464397743360821645341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9990571727315628857720909 3746464397743360821645341)
                    ·
                      refine ⟨1404924149153760308117003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3746464397743360821645341 1404924149153760308117003)
                      ·
                        rfl

theorem cell23_2736080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_2736080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736080 prefixEnd_2736080 := by exact prefixLift 2736080
  have htrace : WordTrace (prefixWord ++ tailWord_2736080) baseStart_2736080 baseEnd_2736080 := by
    simpa [prefixWord, tailWord_2736080, baseEnd_2736080] using wordTrace_append hprefix tailTrace_2736080
  have hstable : (prefixWord ++ tailWord_2736080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736080).length < 2 ^ (prefixWord ++ tailWord_2736080).sum := by decide
  have hdescent : baseEnd_2736080 < baseStart_2736080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736098 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_2736098 : Nat := 118140960795 + 2736098 * 2 ^ 59
def prefixEnd_2736098 : Nat := 4983230072969 + 3 ^ 40 * 2736098 * 2
def baseEnd_2736098 : Nat := 1404933391805541237691921

theorem tailTrace_2736098 : CollatzResearch.WordTrace tailWord_2736098 prefixEnd_2736098 1404933391805541237691921 := by
  unfold tailWord_2736098
  simp only [CollatzResearch.WordTrace]
  refine ⟨24948423110397927295196237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66529128294394472787189965 24948423110397927295196237)
  ·
    refine ⟨9355658666399222735698589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24948423110397927295196237 9355658666399222735698589)
    ·
      refine ⟨3508371999899708525886971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9355658666399222735698589 3508371999899708525886971)
      ·
        refine ⟨5262557999849562788830457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3508371999899708525886971 5262557999849562788830457)
        ·
          refine ⟨3946918499887172091622843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5262557999849562788830457 3946918499887172091622843)
          ·
            refine ⟨5920377749830758137434265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946918499887172091622843 5920377749830758137434265)
            ·
              refine ⟨4440283312373068603075699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5920377749830758137434265 4440283312373068603075699)
              ·
                refine ⟨6660424968559602904613549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4440283312373068603075699 6660424968559602904613549)
                ·
                  refine ⟨2497659363209851089230081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6660424968559602904613549 2497659363209851089230081)
                  ·
                    refine ⟨1873244522407388316922561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2497659363209851089230081 1873244522407388316922561)
                    ·
                      refine ⟨1404933391805541237691921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873244522407388316922561 1404933391805541237691921)
                      ·
                        rfl

theorem cell23_2736098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_2736098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736098 prefixEnd_2736098 := by exact prefixLift 2736098
  have htrace : WordTrace (prefixWord ++ tailWord_2736098) baseStart_2736098 baseEnd_2736098 := by
    simpa [prefixWord, tailWord_2736098, baseEnd_2736098] using wordTrace_append hprefix tailTrace_2736098
  have hstable : (prefixWord ++ tailWord_2736098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736098).length < 2 ^ (prefixWord ++ tailWord_2736098).sum := by decide
  have hdescent : baseEnd_2736098 < baseStart_2736098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736124 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_2736124 : Nat := 118140960795 + 2736124 * 2 ^ 59
def prefixEnd_2736124 : Nat := 4983230072969 + 3 ^ 40 * 2736124 * 2
def baseEnd_2736124 : Nat := 1404946742302558135966801

theorem tailTrace_2736124 : CollatzResearch.WordTrace tailWord_2736124 prefixEnd_2736124 1404946742302558135966801 := by
  unfold tailWord_2736124
  simp only [CollatzResearch.WordTrace]
  refine ⟨49897320369748757810615713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66529760492998343747487617 49897320369748757810615713)
  ·
    refine ⟨37422990277311568357961785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49897320369748757810615713 37422990277311568357961785)
    ·
      refine ⟨28067242707983676268471339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37422990277311568357961785 28067242707983676268471339)
      ·
        refine ⟨42100864061975514402707009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28067242707983676268471339 42100864061975514402707009)
        ·
          refine ⟨31575648046481635802030257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42100864061975514402707009 31575648046481635802030257)
          ·
            refine ⟨23681736034861226851522693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31575648046481635802030257 23681736034861226851522693)
            ·
              refine ⟨4440325506536480034660505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23681736034861226851522693 4440325506536480034660505)
              ·
                refine ⟨3330244129902360025995379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4440325506536480034660505 3330244129902360025995379)
                ·
                  refine ⟨4995366194853540038993069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330244129902360025995379 4995366194853540038993069)
                  ·
                    refine ⟨1873262323070077514622401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4995366194853540038993069 1873262323070077514622401)
                    ·
                      refine ⟨1404946742302558135966801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873262323070077514622401 1404946742302558135966801)
                      ·
                        rfl

theorem cell23_2736124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_2736124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736124 prefixEnd_2736124 := by exact prefixLift 2736124
  have htrace : WordTrace (prefixWord ++ tailWord_2736124) baseStart_2736124 baseEnd_2736124 := by
    simpa [prefixWord, tailWord_2736124, baseEnd_2736124] using wordTrace_append hprefix tailTrace_2736124
  have hstable : (prefixWord ++ tailWord_2736124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736124).length < 2 ^ (prefixWord ++ tailWord_2736124).sum := by decide
  have hdescent : baseEnd_2736124 < baseStart_2736124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736132 : List Nat := [2, 3, 2, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2736132 : Nat := 118140960795 + 2736132 * 2 ^ 59
def prefixEnd_2736132 : Nat := 4983230072969 + 3 ^ 40 * 2736132 * 2
def baseEnd_2736132 : Nat := 1404950850147794104666765

theorem tailTrace_2736132 : CollatzResearch.WordTrace tailWord_2736132 prefixEnd_2736132 1404950850147794104666765 := by
  unfold tailWord_2736132
  simp only [CollatzResearch.WordTrace]
  refine ⟨49897466261734266493761325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66529955015645688658348433 49897466261734266493761325)
  ·
    refine ⟨18711549848150349935160497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49897466261734266493761325 18711549848150349935160497)
    ·
      refine ⟨14033662386112762451370373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18711549848150349935160497 14033662386112762451370373)
      ·
        refine ⟨2631311697396142959631945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14033662386112762451370373 2631311697396142959631945)
        ·
          refine ⟨1973483773047107219723959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2631311697396142959631945 1973483773047107219723959)
          ·
            refine ⟨2960225659570660829585939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973483773047107219723959 2960225659570660829585939)
            ·
              refine ⟨4440338489355991244378909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960225659570660829585939 4440338489355991244378909)
              ·
                refine ⟨1665126933508496716642091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4440338489355991244378909 1665126933508496716642091)
                ·
                  refine ⟨2497690400262745074963137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665126933508496716642091 2497690400262745074963137)
                  ·
                    refine ⟨1873267800197058806222353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2497690400262745074963137 1873267800197058806222353)
                    ·
                      refine ⟨1404950850147794104666765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873267800197058806222353 1404950850147794104666765)
                      ·
                        rfl

theorem cell23_2736132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2736132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736132 prefixEnd_2736132 := by exact prefixLift 2736132
  have htrace : WordTrace (prefixWord ++ tailWord_2736132) baseStart_2736132 baseEnd_2736132 := by
    simpa [prefixWord, tailWord_2736132, baseEnd_2736132] using wordTrace_append hprefix tailTrace_2736132
  have hstable : (prefixWord ++ tailWord_2736132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736132).length < 2 ^ (prefixWord ++ tailWord_2736132).sum := by decide
  have hdescent : baseEnd_2736132 < baseStart_2736132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736140 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2736140 : Nat := 118140960795 + 2736140 * 2 ^ 59
def prefixEnd_2736140 : Nat := 4983230072969 + 3 ^ 40 * 2736140 * 2
def baseEnd_2736140 : Nat := 1404954957993030073366727

theorem tailTrace_2736140 : CollatzResearch.WordTrace tailWord_2736140 prefixEnd_2736140 1404954957993030073366727 := by
  unfold tailWord_2736140
  simp only [CollatzResearch.WordTrace]
  refine ⟨49897612153719775176906937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66530149538293033569209249 49897612153719775176906937)
  ·
    refine ⟨37423209115289831382680203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49897612153719775176906937 37423209115289831382680203)
    ·
      refine ⟨56134813672934747074020305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37423209115289831382680203 56134813672934747074020305)
      ·
        refine ⟨42101110254701060305515229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56134813672934747074020305 42101110254701060305515229)
        ·
          refine ⟨15787916345512897614568211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42101110254701060305515229 15787916345512897614568211)
          ·
            refine ⟨23681874518269346421852317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15787916345512897614568211 23681874518269346421852317)
            ·
              refine ⟨8880702944351004908194619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23681874518269346421852317 8880702944351004908194619)
              ·
                refine ⟨13321054416526507362291929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8880702944351004908194619 13321054416526507362291929)
                ·
                  refine ⟨9990790812394880521718947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13321054416526507362291929 9990790812394880521718947)
                  ·
                    refine ⟨14986186218592320782578421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9990790812394880521718947 14986186218592320782578421)
                    ·
                      refine ⟨1404954957993030073366727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14986186218592320782578421 1404954957993030073366727)
                      ·
                        rfl

theorem cell23_2736140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2736140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736140 prefixEnd_2736140 := by exact prefixLift 2736140
  have htrace : WordTrace (prefixWord ++ tailWord_2736140) baseStart_2736140 baseEnd_2736140 := by
    simpa [prefixWord, tailWord_2736140, baseEnd_2736140] using wordTrace_append hprefix tailTrace_2736140
  have hstable : (prefixWord ++ tailWord_2736140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736140).length < 2 ^ (prefixWord ++ tailWord_2736140).sum := by decide
  have hdescent : baseEnd_2736140 < baseStart_2736140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736153 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2736153 : Nat := 118140960795 + 2736153 * 2 ^ 59
def prefixEnd_2736153 : Nat := 4983230072969 + 3 ^ 40 * 2736153 * 2
def baseEnd_2736153 : Nat := 1404961633241538522504167

theorem tailTrace_2736153 : CollatzResearch.WordTrace tailWord_2736153 prefixEnd_2736153 1404961633241538522504167 := by
  unfold tailWord_2736153
  simp only [CollatzResearch.WordTrace]
  refine ⟨99795698456392453574037113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66530465637594969049358075 99795698456392453574037113)
  ·
    refine ⟨74846773842294340180527835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99795698456392453574037113 74846773842294340180527835)
    ·
      refine ⟨112270160763441510270791753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74846773842294340180527835 112270160763441510270791753)
      ·
        refine ⟨84202620572581132703093815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112270160763441510270791753 84202620572581132703093815)
        ·
          refine ⟨126303930858871699054640723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84202620572581132703093815 126303930858871699054640723)
          ·
            refine ⟨189455896288307548581961085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126303930858871699054640723 189455896288307548581961085)
            ·
              refine ⟨71045961108115330718235407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189455896288307548581961085 71045961108115330718235407)
              ·
                refine ⟨106568941662172996077353111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71045961108115330718235407 106568941662172996077353111)
                ·
                  refine ⟨159853412493259494116029667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106568941662172996077353111 159853412493259494116029667)
                  ·
                    refine ⟨239780118739889241174044501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159853412493259494116029667 239780118739889241174044501)
                    ·
                      refine ⟨1404961633241538522504167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 239780118739889241174044501 1404961633241538522504167)
                      ·
                        rfl

theorem cell23_2736153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2736153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736153 prefixEnd_2736153 := by exact prefixLift 2736153
  have htrace : WordTrace (prefixWord ++ tailWord_2736153) baseStart_2736153 baseEnd_2736153 := by
    simpa [prefixWord, tailWord_2736153, baseEnd_2736153] using wordTrace_append hprefix tailTrace_2736153
  have hstable : (prefixWord ++ tailWord_2736153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736153).length < 2 ^ (prefixWord ++ tailWord_2736153).sum := by decide
  have hdescent : baseEnd_2736153 < baseStart_2736153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736154 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2]
def baseStart_2736154 : Nat := 118140960795 + 2736154 * 2 ^ 59
def prefixEnd_2736154 : Nat := 4983230072969 + 3 ^ 40 * 2736154 * 2
def baseEnd_2736154 : Nat := 1404962146722193018591663

theorem tailTrace_2736154 : CollatzResearch.WordTrace tailWord_2736154 prefixEnd_2736154 1404962146722193018591663 := by
  unfold tailWord_2736154
  simp only [CollatzResearch.WordTrace]
  refine ⟨24948933732347207686205879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66530489952925887163215677 24948933732347207686205879)
  ·
    refine ⟨37423400598520811529308819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24948933732347207686205879 37423400598520811529308819)
    ·
      refine ⟨56135100897781217293963229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37423400598520811529308819 56135100897781217293963229)
      ·
        refine ⟨21050662836667956485236211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56135100897781217293963229 21050662836667956485236211)
        ·
          refine ⟨31575994255001934727854317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21050662836667956485236211 31575994255001934727854317)
          ·
            refine ⟨11840997845625725522945369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31575994255001934727854317 11840997845625725522945369)
            ·
              refine ⟨8880748384219294142209027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11840997845625725522945369 8880748384219294142209027)
              ·
                refine ⟨13321122576328941213313541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8880748384219294142209027 13321122576328941213313541)
                ·
                  refine ⟨2497710483061676477496289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13321122576328941213313541 2497710483061676477496289)
                  ·
                    refine ⟨1873282862296257358122217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2497710483061676477496289 1873282862296257358122217)
                    ·
                      refine ⟨1404962146722193018591663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873282862296257358122217 1404962146722193018591663)
                      ·
                        rfl

theorem cell23_2736154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_2736154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736154 prefixEnd_2736154 := by exact prefixLift 2736154
  have htrace : WordTrace (prefixWord ++ tailWord_2736154) baseStart_2736154 baseEnd_2736154 := by
    simpa [prefixWord, tailWord_2736154, baseEnd_2736154] using wordTrace_append hprefix tailTrace_2736154
  have hstable : (prefixWord ++ tailWord_2736154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736154).length < 2 ^ (prefixWord ++ tailWord_2736154).sum := by decide
  have hdescent : baseEnd_2736154 < baseStart_2736154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736227 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 1, 6, 2]
def baseStart_2736227 : Nat := 118140960795 + 2736227 * 2 ^ 59
def prefixEnd_2736227 : Nat := 4983230072969 + 3 ^ 40 * 2736227 * 2
def baseEnd_2736227 : Nat := 1404999630809971232978827

theorem tailTrace_2736227 : CollatzResearch.WordTrace tailWord_2736227 prefixEnd_2736227 1404999630809971232978827 := by
  unfold tailWord_2736227
  simp only [CollatzResearch.WordTrace]
  refine ⟨99798397458124364212230935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66532264972082909474820623 99798397458124364212230935)
  ·
    refine ⟨149697596187186546318346403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99798397458124364212230935 149697596187186546318346403)
    ·
      refine ⟨224546394280779819477519605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149697596187186546318346403 224546394280779819477519605)
      ·
        refine ⟨21051224463823108076017463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224546394280779819477519605 21051224463823108076017463)
        ·
          refine ⟨31576836695734662114026195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21051224463823108076017463 31576836695734662114026195)
          ·
            refine ⟨47365255043601993171039293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31576836695734662114026195 47365255043601993171039293)
            ·
              refine ⟨17761970641350747439139735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47365255043601993171039293 17761970641350747439139735)
              ·
                refine ⟨26642955962026121158709603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17761970641350747439139735 26642955962026121158709603)
                ·
                  refine ⟨39964433943039181738064405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26642955962026121158709603 39964433943039181738064405)
                  ·
                    refine ⟨1873332841079961643971769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39964433943039181738064405 1873332841079961643971769)
                    ·
                      refine ⟨1404999630809971232978827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873332841079961643971769 1404999630809971232978827)
                      ·
                        rfl

theorem cell23_2736227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_2736227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736227 prefixEnd_2736227 := by exact prefixLift 2736227
  have htrace : WordTrace (prefixWord ++ tailWord_2736227) baseStart_2736227 baseEnd_2736227 := by
    simpa [prefixWord, tailWord_2736227, baseEnd_2736227] using wordTrace_append hprefix tailTrace_2736227
  have hstable : (prefixWord ++ tailWord_2736227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736227).length < 2 ^ (prefixWord ++ tailWord_2736227).sum := by decide
  have hdescent : baseEnd_2736227 < baseStart_2736227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736247 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_2736247 : Nat := 118140960795 + 2736247 * 2 ^ 59
def prefixEnd_2736247 : Nat := 4983230072969 + 3 ^ 40 * 2736247 * 2
def baseEnd_2736247 : Nat := 1405009900423061154728735

theorem tailTrace_2736247 : CollatzResearch.WordTrace tailWord_2736247 prefixEnd_2736247 1405009900423061154728735 := by
  unfold tailWord_2736247
  simp only [CollatzResearch.WordTrace]
  refine ⟨99799126918051907627958995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66532751278701271751972663 99799126918051907627958995)
  ·
    refine ⟨149698690377077861441938493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99799126918051907627958995 149698690377077861441938493)
    ·
      refine ⟨56137008891404198040726935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149698690377077861441938493 56137008891404198040726935)
      ·
        refine ⟨84205513337106297061090403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56137008891404198040726935 84205513337106297061090403)
        ·
          refine ⟨126308270005659445591635605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84205513337106297061090403 126308270005659445591635605)
          ·
            refine ⟨5920700156515286512107919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126308270005659445591635605 5920700156515286512107919)
            ·
              refine ⟨8881050234772929768161879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5920700156515286512107919 8881050234772929768161879)
              ·
                refine ⟨13321575352159394652242819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8881050234772929768161879 13321575352159394652242819)
                ·
                  refine ⟨19982363028239091978364229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13321575352159394652242819 19982363028239091978364229)
                  ·
                    refine ⟨3746693067794829745943293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19982363028239091978364229 3746693067794829745943293)
                    ·
                      refine ⟨1405009900423061154728735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3746693067794829745943293 1405009900423061154728735)
                      ·
                        rfl

theorem cell23_2736247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_2736247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736247 prefixEnd_2736247 := by exact prefixLift 2736247
  have htrace : WordTrace (prefixWord ++ tailWord_2736247) baseStart_2736247 baseEnd_2736247 := by
    simpa [prefixWord, tailWord_2736247, baseEnd_2736247] using wordTrace_append hprefix tailTrace_2736247
  have hstable : (prefixWord ++ tailWord_2736247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736247).length < 2 ^ (prefixWord ++ tailWord_2736247).sum := by decide
  have hdescent : baseEnd_2736247 < baseStart_2736247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736284 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 6]
def baseStart_2736284 : Nat := 118140960795 + 2736284 * 2 ^ 59
def prefixEnd_2736284 : Nat := 4983230072969 + 3 ^ 40 * 2736284 * 2
def baseEnd_2736284 : Nat := 156114322134141945551785

theorem tailTrace_2736284 : CollatzResearch.WordTrace tailWord_2736284 prefixEnd_2736284 156114322134141945551785 := by
  unfold tailWord_2736284
  simp only [CollatzResearch.WordTrace]
  refine ⟨49900238209458931473527953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66533650945945241964703937 49900238209458931473527953)
  ·
    refine ⟨37425178657094198605145965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49900238209458931473527953 37425178657094198605145965)
    ·
      refine ⟨14034441996410324476929737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37425178657094198605145965 14034441996410324476929737)
      ·
        refine ⟨10525831497307743357697303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14034441996410324476929737 10525831497307743357697303)
        ·
          refine ⟨15788747245961615036545955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10525831497307743357697303 15788747245961615036545955)
          ·
            refine ⟨23683120868942422554818933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15788747245961615036545955 23683120868942422554818933)
            ·
              refine ⟨2220292581463352114514275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23683120868942422554818933 2220292581463352114514275)
              ·
                refine ⟨3330438872195028171771413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220292581463352114514275 3330438872195028171771413)
                ·
                  refine ⟨156114322134141945551785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3330438872195028171771413 156114322134141945551785)
                  ·
                    rfl

theorem cell23_2736284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_2736284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736284 prefixEnd_2736284 := by exact prefixLift 2736284
  have htrace : WordTrace (prefixWord ++ tailWord_2736284) baseStart_2736284 baseEnd_2736284 := by
    simpa [prefixWord, tailWord_2736284, baseEnd_2736284] using wordTrace_append hprefix tailTrace_2736284
  have hstable : (prefixWord ++ tailWord_2736284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736284).length < 2 ^ (prefixWord ++ tailWord_2736284).sum := by decide
  have hdescent : baseEnd_2736284 < baseStart_2736284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736305 : List Nat := [1, 2, 2, 5, 3, 1, 1, 3, 1, 4]
def baseStart_2736305 : Nat := 118140960795 + 2736305 * 2 ^ 59
def prefixEnd_2736305 : Nat := 4983230072969 + 3 ^ 40 * 2736305 * 2
def baseEnd_2736305 : Nat := 468346560767007309267823

theorem tailTrace_2736305 : CollatzResearch.WordTrace tailWord_2736305 prefixEnd_2736305 468346560767007309267823 := by
  unfold tailWord_2736305
  simp only [CollatzResearch.WordTrace]
  refine ⟨99801242351841783533570369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66534161567894522355713579 99801242351841783533570369)
  ·
    refine ⟨74850931763881337650177777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99801242351841783533570369 74850931763881337650177777)
    ·
      refine ⟨56138198822911003237633333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74850931763881337650177777 56138198822911003237633333)
      ·
        refine ⟨5262956139647906553528125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56138198822911003237633333 5262956139647906553528125)
        ·
          refine ⟨1973608552367964957573047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5262956139647906553528125 1973608552367964957573047)
          ·
            refine ⟨2960412828551947436359571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973608552367964957573047 2960412828551947436359571)
            ·
              refine ⟨4440619242827921154539357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960412828551947436359571 4440619242827921154539357)
              ·
                refine ⟨1665232216060470432952259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4440619242827921154539357 1665232216060470432952259)
                ·
                  refine ⟨2497848324090705649428389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665232216060470432952259 2497848324090705649428389)
                  ·
                    refine ⟨468346560767007309267823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2497848324090705649428389 468346560767007309267823)
                    ·
                      rfl

theorem cell23_2736305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_2736305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736305 prefixEnd_2736305 := by exact prefixLift 2736305
  have htrace : WordTrace (prefixWord ++ tailWord_2736305) baseStart_2736305 baseEnd_2736305 := by
    simpa [prefixWord, tailWord_2736305, baseEnd_2736305] using wordTrace_append hprefix tailTrace_2736305
  have hstable : (prefixWord ++ tailWord_2736305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736305).length < 2 ^ (prefixWord ++ tailWord_2736305).sum := by decide
  have hdescent : baseEnd_2736305 < baseStart_2736305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736317 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2736317 : Nat := 118140960795 + 2736317 * 2 ^ 59
def prefixEnd_2736317 : Nat := 4983230072969 + 3 ^ 40 * 2736317 * 2
def baseEnd_2736317 : Nat := 1405045844068875880853413

theorem tailTrace_2736317 : CollatzResearch.WordTrace tailWord_2736317 prefixEnd_2736317 1405045844068875880853413 := by
  unfold tailWord_2736317
  simp only [CollatzResearch.WordTrace]
  refine ⟨99801680027798309583007205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66534453351865539722004803 99801680027798309583007205)
  ·
    refine ⟨18712815005212183046813851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99801680027798309583007205 18712815005212183046813851)
    ·
      refine ⟨28069222507818274570220777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18712815005212183046813851 28069222507818274570220777)
      ·
        refine ⟨21051916880863705927665583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28069222507818274570220777 21051916880863705927665583)
        ·
          refine ⟨31577875321295558891498375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21051916880863705927665583 31577875321295558891498375)
          ·
            refine ⟨47366812981943338337247563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31577875321295558891498375 47366812981943338337247563)
            ·
              refine ⟨71050219472915007505871345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47366812981943338337247563 71050219472915007505871345)
              ·
                refine ⟨53287664604686255629403509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71050219472915007505871345 53287664604686255629403509)
                ·
                  refine ⟨4995718556689336465256579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53287664604686255629403509 4995718556689336465256579)
                  ·
                    refine ⟨7493577835034004697884869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4995718556689336465256579 7493577835034004697884869)
                    ·
                      refine ⟨1405045844068875880853413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7493577835034004697884869 1405045844068875880853413)
                      ·
                        rfl

theorem cell23_2736317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2736317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736317 prefixEnd_2736317 := by exact prefixLift 2736317
  have htrace : WordTrace (prefixWord ++ tailWord_2736317) baseStart_2736317 baseEnd_2736317 := by
    simpa [prefixWord, tailWord_2736317, baseEnd_2736317] using wordTrace_append hprefix tailTrace_2736317
  have hstable : (prefixWord ++ tailWord_2736317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736317).length < 2 ^ (prefixWord ++ tailWord_2736317).sum := by decide
  have hdescent : baseEnd_2736317 < baseStart_2736317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736322 : List Nat := [3, 5, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2736322 : Nat := 118140960795 + 2736322 * 2 ^ 59
def prefixEnd_2736322 : Nat := 4983230072969 + 3 ^ 40 * 2736322 * 2
def baseEnd_2736322 : Nat := 468349470490716120430297

theorem tailTrace_2736322 : CollatzResearch.WordTrace tailWord_2736322 prefixEnd_2736322 468349470490716120430297 := by
  unfold tailWord_2736322
  simp only [CollatzResearch.WordTrace]
  refine ⟨24950465598195048859234805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66534574928520130291292813 24950465598195048859234805)
  ·
    refine ⟨2339106149830785830553263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24950465598195048859234805 2339106149830785830553263)
    ·
      refine ⟨3508659224746178745829895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339106149830785830553263 3508659224746178745829895)
      ·
        refine ⟨5262988837119268118744843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3508659224746178745829895 5262988837119268118744843)
        ·
          refine ⟨7894483255678902178117265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5262988837119268118744843 7894483255678902178117265)
          ·
            refine ⟨5920862441759176633587949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7894483255678902178117265 5920862441759176633587949)
            ·
              refine ⟨2220323415659691237595481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5920862441759176633587949 2220323415659691237595481)
              ·
                refine ⟨1665242561744768428196611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2220323415659691237595481 1665242561744768428196611)
                ·
                  refine ⟨2497863842617152642294917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665242561744768428196611 2497863842617152642294917)
                  ·
                    refine ⟨468349470490716120430297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2497863842617152642294917 468349470490716120430297)
                    ·
                      rfl

theorem cell23_2736322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2736322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736322 prefixEnd_2736322 := by exact prefixLift 2736322
  have htrace : WordTrace (prefixWord ++ tailWord_2736322) baseStart_2736322 baseEnd_2736322 := by
    simpa [prefixWord, tailWord_2736322, baseEnd_2736322] using wordTrace_append hprefix tailTrace_2736322
  have hstable : (prefixWord ++ tailWord_2736322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736322).length < 2 ^ (prefixWord ++ tailWord_2736322).sum := by decide
  have hdescent : baseEnd_2736322 < baseStart_2736322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736337 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_2736337 : Nat := 118140960795 + 2736337 * 2 ^ 59
def prefixEnd_2736337 : Nat := 4983230072969 + 3 ^ 40 * 2736337 * 2
def baseEnd_2736337 : Nat := 1405056113681965802603321

theorem tailTrace_2736337 : CollatzResearch.WordTrace tailWord_2736337 prefixEnd_2736337 1405056113681965802603321 := by
  unfold tailWord_2736337
  simp only [CollatzResearch.WordTrace]
  refine ⟨99802409487725852998735265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66534939658483901999156843 99802409487725852998735265)
  ·
    refine ⟨74851807115794389749051449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99802409487725852998735265 74851807115794389749051449)
    ·
      refine ⟨56138855336845792311788587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74851807115794389749051449 56138855336845792311788587)
      ·
        refine ⟨84208283005268688467682881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56138855336845792311788587 84208283005268688467682881)
        ·
          refine ⟨63156212253951516350762161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84208283005268688467682881 63156212253951516350762161)
          ·
            refine ⟨47367159190463637263071621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63156212253951516350762161 47367159190463637263071621)
            ·
              refine ⟨8881342348211931986825929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47367159190463637263071621 8881342348211931986825929)
              ·
                refine ⟨6661006761158948990119447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8881342348211931986825929 6661006761158948990119447)
                ·
                  refine ⟨9991510141738423485179171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6661006761158948990119447 9991510141738423485179171)
                  ·
                    refine ⟨14987265212607635227768757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9991510141738423485179171 14987265212607635227768757)
                    ·
                      refine ⟨1405056113681965802603321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14987265212607635227768757 1405056113681965802603321)
                      ·
                        rfl

theorem cell23_2736337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_2736337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736337 prefixEnd_2736337 := by exact prefixLift 2736337
  have htrace : WordTrace (prefixWord ++ tailWord_2736337) baseStart_2736337 baseEnd_2736337 := by
    simpa [prefixWord, tailWord_2736337, baseEnd_2736337] using wordTrace_append hprefix tailTrace_2736337
  have hstable : (prefixWord ++ tailWord_2736337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736337).length < 2 ^ (prefixWord ++ tailWord_2736337).sum := by decide
  have hdescent : baseEnd_2736337 < baseStart_2736337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736357 : List Nat := [1, 3, 1, 4, 2, 1, 2, 9]
def baseStart_2736357 : Nat := 118140960795 + 2736357 * 2 ^ 59
def prefixEnd_2736357 : Nat := 4983230072969 + 3 ^ 40 * 2736357 * 2
def baseEnd_2736357 : Nat := 52039495677594656457527

theorem tailTrace_2736357 : CollatzResearch.WordTrace tailWord_2736357 prefixEnd_2736357 52039495677594656457527 := by
  unfold tailWord_2736357
  simp only [CollatzResearch.WordTrace]
  refine ⟨99803138947653396414463325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66535425965102264276308883 99803138947653396414463325)
  ·
    refine ⟨37426177105370023655423747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99803138947653396414463325 37426177105370023655423747)
    ·
      refine ⟨56139265658055035483135621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37426177105370023655423747 56139265658055035483135621)
      ·
        refine ⟨10526112310885319153087929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56139265658055035483135621 10526112310885319153087929)
        ·
          refine ⟨7894584233163989364815947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10526112310885319153087929 7894584233163989364815947)
          ·
            refine ⟨11841876349745984047223921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7894584233163989364815947 11841876349745984047223921)
            ·
              refine ⟨8881407262309488035417941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11841876349745984047223921 8881407262309488035417941)
              ·
                refine ⟨52039495677594656457527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8881407262309488035417941 52039495677594656457527)
                ·
                  rfl

theorem cell23_2736357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 9].length) (baseStart_2736357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736357 prefixEnd_2736357 := by exact prefixLift 2736357
  have htrace : WordTrace (prefixWord ++ tailWord_2736357) baseStart_2736357 baseEnd_2736357 := by
    simpa [prefixWord, tailWord_2736357, baseEnd_2736357] using wordTrace_append hprefix tailTrace_2736357
  have hstable : (prefixWord ++ tailWord_2736357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736357).length < 2 ^ (prefixWord ++ tailWord_2736357).sum := by decide
  have hdescent : baseEnd_2736357 < baseStart_2736357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736371 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 1, 2, 3]
def baseStart_2736371 : Nat := 118140960795 + 2736371 * 2 ^ 59
def prefixEnd_2736371 : Nat := 4983230072969 + 3 ^ 40 * 2736371 * 2
def baseEnd_2736371 : Nat := 1405073572024218669578165

theorem tailTrace_2736371 : CollatzResearch.WordTrace tailWord_2736371 prefixEnd_2736371 1405073572024218669578165 := by
  unfold tailWord_2736371
  simp only [CollatzResearch.WordTrace]
  refine ⟨99803649569602676805472967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66535766379735117870315311 99803649569602676805472967)
  ·
    refine ⟨149705474354404015208209451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99803649569602676805472967 149705474354404015208209451)
    ·
      refine ⟨224558211531606022812314177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149705474354404015208209451 224558211531606022812314177)
      ·
        refine ⟨168418658648704517109235633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224558211531606022812314177 168418658648704517109235633)
        ·
          refine ⟨126313993986528387831926725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168418658648704517109235633 126313993986528387831926725)
          ·
            refine ⟨23683873872474072718486261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126313993986528387831926725 23683873872474072718486261)
            ·
              refine ⟨2220363175544444317358087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23683873872474072718486261 2220363175544444317358087)
              ·
                refine ⟨3330544763316666476037131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220363175544444317358087 3330544763316666476037131)
                ·
                  refine ⟨4995817144974999714055697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330544763316666476037131 4995817144974999714055697)
                  ·
                    refine ⟨3746862858731249785541773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4995817144974999714055697 3746862858731249785541773)
                    ·
                      refine ⟨1405073572024218669578165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3746862858731249785541773 1405073572024218669578165)
                      ·
                        rfl

theorem cell23_2736371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 2, 3].length) (baseStart_2736371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736371 prefixEnd_2736371 := by exact prefixLift 2736371
  have htrace : WordTrace (prefixWord ++ tailWord_2736371) baseStart_2736371 baseEnd_2736371 := by
    simpa [prefixWord, tailWord_2736371, baseEnd_2736371] using wordTrace_append hprefix tailTrace_2736371
  have hstable : (prefixWord ++ tailWord_2736371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736371).length < 2 ^ (prefixWord ++ tailWord_2736371).sum := by decide
  have hdescent : baseEnd_2736371 < baseStart_2736371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736384 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 4, 1, 3]
def baseStart_2736384 : Nat := 118140960795 + 2736384 * 2 ^ 59
def prefixEnd_2736384 : Nat := 4983230072969 + 3 ^ 40 * 2736384 * 2
def baseEnd_2736384 : Nat := 1405080247272727118715605

theorem tailTrace_2736384 : CollatzResearch.WordTrace tailWord_2736384 prefixEnd_2736384 1405080247272727118715605 := by
  unfold tailWord_2736384
  simp only [CollatzResearch.WordTrace]
  refine ⟨49902061859277790012848103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66536082479037053350464137 49902061859277790012848103)
  ·
    refine ⟨74853092788916685019272155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49902061859277790012848103 74853092788916685019272155)
    ·
      refine ⟨112279639183375027528908233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74853092788916685019272155 112279639183375027528908233)
      ·
        refine ⟨84209729387531270646681175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112279639183375027528908233 84209729387531270646681175)
        ·
          refine ⟨126314594081296905970021763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84209729387531270646681175 126314594081296905970021763)
          ·
            refine ⟨189471891121945358955032645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126314594081296905970021763 189471891121945358955032645)
            ·
              refine ⟨35525979585364754804068621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189471891121945358955032645 35525979585364754804068621)
              ·
                refine ⟨13322242344511783051525733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35525979585364754804068621 13322242344511783051525733)
                ·
                  refine ⟨2497920439595959322161075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13322242344511783051525733 2497920439595959322161075)
                  ·
                    refine ⟨3746880659393938983241613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2497920439595959322161075 3746880659393938983241613)
                    ·
                      refine ⟨1405080247272727118715605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3746880659393938983241613 1405080247272727118715605)
                      ·
                        rfl

theorem cell23_2736384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_2736384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736384 prefixEnd_2736384 := by exact prefixLift 2736384
  have htrace : WordTrace (prefixWord ++ tailWord_2736384) baseStart_2736384 baseEnd_2736384 := by
    simpa [prefixWord, tailWord_2736384, baseEnd_2736384] using wordTrace_append hprefix tailTrace_2736384
  have hstable : (prefixWord ++ tailWord_2736384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736384).length < 2 ^ (prefixWord ++ tailWord_2736384).sum := by decide
  have hdescent : baseEnd_2736384 < baseStart_2736384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736391 : List Nat := [1, 1, 4, 5, 1, 2, 1, 8]
def baseStart_2736391 : Nat := 118140960795 + 2736391 * 2 ^ 59
def prefixEnd_2736391 : Nat := 4983230072969 + 3 ^ 40 * 2736391 * 2
def baseEnd_2736391 : Nat := 52040142282863281160299

theorem tailTrace_2736391 : CollatzResearch.WordTrace tailWord_2736391 prefixEnd_2736391 52040142282863281160299 := by
  unfold tailWord_2736391
  simp only [CollatzResearch.WordTrace]
  refine ⟨99804379029530220221201027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66536252686353480147467351 99804379029530220221201027)
  ·
    refine ⟨149706568544295330331801541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99804379029530220221201027 149706568544295330331801541)
    ·
      refine ⟨28069981602055374437212789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149706568544295330331801541 28069981602055374437212789)
      ·
        refine ⟨2631560775192691353488699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28069981602055374437212789 2631560775192691353488699)
        ·
          refine ⟨3947341162789037030233049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2631560775192691353488699 3947341162789037030233049)
          ·
            refine ⟨2960505872091777772674787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3947341162789037030233049 2960505872091777772674787)
            ·
              refine ⟨4440758808137666659012181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960505872091777772674787 4440758808137666659012181)
              ·
                refine ⟨52040142282863281160299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4440758808137666659012181 52040142282863281160299)
                ·
                  rfl

theorem cell23_2736391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 8].length) (baseStart_2736391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736391 prefixEnd_2736391 := by exact prefixLift 2736391
  have htrace : WordTrace (prefixWord ++ tailWord_2736391) baseStart_2736391 baseEnd_2736391 := by
    simpa [prefixWord, tailWord_2736391, baseEnd_2736391] using wordTrace_append hprefix tailTrace_2736391
  have hstable : (prefixWord ++ tailWord_2736391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736391).length < 2 ^ (prefixWord ++ tailWord_2736391).sum := by decide
  have hdescent : baseEnd_2736391 < baseStart_2736391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736401 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 3]
def baseStart_2736401 : Nat := 118140960795 + 2736401 * 2 ^ 59
def prefixEnd_2736401 : Nat := 4983230072969 + 3 ^ 40 * 2736401 * 2
def baseEnd_2736401 : Nat := 1405088976443853552203027

theorem tailTrace_2736401 : CollatzResearch.WordTrace tailWord_2736401 prefixEnd_2736401 1405088976443853552203027 := by
  unfold tailWord_2736401
  simp only [CollatzResearch.WordTrace]
  refine ⟨99804743759493991929065057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66536495839662661286043371 99804743759493991929065057)
  ·
    refine ⟨74853557819620493946798793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99804743759493991929065057 74853557819620493946798793)
    ·
      refine ⟨56140168364715370460099095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74853557819620493946798793 56140168364715370460099095)
      ·
        refine ⟨84210252547073055690148643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56140168364715370460099095 84210252547073055690148643)
        ·
          refine ⟨126315378820609583535222965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84210252547073055690148643 126315378820609583535222965)
          ·
            refine ⟨11842066764432148456427153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126315378820609583535222965 11842066764432148456427153)
            ·
              refine ⟨8881550073324111342320365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11842066764432148456427153 8881550073324111342320365)
              ·
                refine ⟨3330581277496541753370137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8881550073324111342320365 3330581277496541753370137)
                ·
                  refine ⟨2497935958122406315027603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3330581277496541753370137 2497935958122406315027603)
                  ·
                    refine ⟨3746903937183609472541405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2497935958122406315027603 3746903937183609472541405)
                    ·
                      refine ⟨1405088976443853552203027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3746903937183609472541405 1405088976443853552203027)
                      ·
                        rfl

theorem cell23_2736401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_2736401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736401 prefixEnd_2736401 := by exact prefixLift 2736401
  have htrace : WordTrace (prefixWord ++ tailWord_2736401) baseStart_2736401 baseEnd_2736401 := by
    simpa [prefixWord, tailWord_2736401, baseEnd_2736401] using wordTrace_append hprefix tailTrace_2736401
  have hstable : (prefixWord ++ tailWord_2736401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736401).length < 2 ^ (prefixWord ++ tailWord_2736401).sum := by decide
  have hdescent : baseEnd_2736401 < baseStart_2736401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736428 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 1, 3, 2]
def baseStart_2736428 : Nat := 118140960795 + 2736428 * 2 ^ 59
def prefixEnd_2736428 : Nat := 4983230072969 + 3 ^ 40 * 2736428 * 2
def baseEnd_2736428 : Nat := 1405102840421524946565403

theorem tailTrace_2736428 : CollatzResearch.WordTrace tailWord_2736428 prefixEnd_2736428 1405102840421524946565403 := by
  unfold tailWord_2736428
  simp only [CollatzResearch.WordTrace]
  refine ⟨49902864265198087770148969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66537152353597450360198625 49902864265198087770148969)
  ·
    refine ⟨37427148198898565827611727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49902864265198087770148969 37427148198898565827611727)
    ·
      refine ⟨56140722298347848741417591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37427148198898565827611727 56140722298347848741417591)
      ·
        refine ⟨84211083447521773112126387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56140722298347848741417591 84211083447521773112126387)
        ·
          refine ⟨126316625171282659668189581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84211083447521773112126387 126316625171282659668189581)
          ·
            refine ⟨47368734439230997375571093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126316625171282659668189581 47368734439230997375571093)
            ·
              refine ⟨2220409426838953001979895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47368734439230997375571093 2220409426838953001979895)
              ·
                refine ⟨3330614140258429502969843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220409426838953001979895 3330614140258429502969843)
                ·
                  refine ⟨4995921210387644254454765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330614140258429502969843 4995921210387644254454765)
                  ·
                    refine ⟨1873470453895366595420537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4995921210387644254454765 1873470453895366595420537)
                    ·
                      refine ⟨1405102840421524946565403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873470453895366595420537 1405102840421524946565403)
                      ·
                        rfl

theorem cell23_2736428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_2736428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736428 prefixEnd_2736428 := by exact prefixLift 2736428
  have htrace : WordTrace (prefixWord ++ tailWord_2736428) baseStart_2736428 baseEnd_2736428 := by
    simpa [prefixWord, tailWord_2736428, baseEnd_2736428] using wordTrace_append hprefix tailTrace_2736428
  have hstable : (prefixWord ++ tailWord_2736428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736428).length < 2 ^ (prefixWord ++ tailWord_2736428).sum := by decide
  have hdescent : baseEnd_2736428 < baseStart_2736428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736452 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2736452 : Nat := 118140960795 + 2736452 * 2 ^ 59
def prefixEnd_2736452 : Nat := 4983230072969 + 3 ^ 40 * 2736452 * 2
def baseEnd_2736452 : Nat := 1405115163957232852665293

theorem tailTrace_2736452 : CollatzResearch.WordTrace tailWord_2736452 prefixEnd_2736452 1405115163957232852665293 := by
  unfold tailWord_2736452
  simp only [CollatzResearch.WordTrace]
  refine ⟨49903301941154613819585805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66537735921539485092781073 49903301941154613819585805)
  ·
    refine ⟨18713738227932980182344677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49903301941154613819585805 18713738227932980182344677)
    ·
      refine ⟨3508825917737433784189627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18713738227932980182344677 3508825917737433784189627)
      ·
        refine ⟨5263238876606150676284441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3508825917737433784189627 5263238876606150676284441)
        ·
          refine ⟨3947429157454613007213331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5263238876606150676284441 3947429157454613007213331)
          ·
            refine ⟨5921143736181919510819997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947429157454613007213331 5921143736181919510819997)
            ·
              refine ⟨2220428901068219816557499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5921143736181919510819997 2220428901068219816557499)
              ·
                refine ⟨3330643351602329724836249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220428901068219816557499 3330643351602329724836249)
                ·
                  refine ⟨2497982513701747293627187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3330643351602329724836249 2497982513701747293627187)
                  ·
                    refine ⟨3746973770552620940440781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2497982513701747293627187 3746973770552620940440781)
                    ·
                      refine ⟨1405115163957232852665293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3746973770552620940440781 1405115163957232852665293)
                      ·
                        rfl

theorem cell23_2736452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2736452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736452 prefixEnd_2736452 := by exact prefixLift 2736452
  have htrace : WordTrace (prefixWord ++ tailWord_2736452) baseStart_2736452 baseEnd_2736452 := by
    simpa [prefixWord, tailWord_2736452, baseEnd_2736452] using wordTrace_append hprefix tailTrace_2736452
  have hstable : (prefixWord ++ tailWord_2736452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736452).length < 2 ^ (prefixWord ++ tailWord_2736452).sum := by decide
  have hdescent : baseEnd_2736452 < baseStart_2736452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736498 : List Nat := [3, 2, 1, 2, 1, 4, 3, 2, 5]
def baseStart_2736498 : Nat := 118140960795 + 2736498 * 2 ^ 59
def prefixEnd_2736498 : Nat := 4983230072969 + 3 ^ 40 * 2736498 * 2
def baseEnd_2736498 : Nat := 156126531563037741410009

theorem tailTrace_2736498 : CollatzResearch.WordTrace tailWord_2736498 prefixEnd_2736498 156126531563037741410009 := by
  unfold tailWord_2736498
  simp only [CollatzResearch.WordTrace]
  refine ⟨24952070410035644373836537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66538854426761718330230765 24952070410035644373836537)
  ·
    refine ⟨18714052807526733280377403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24952070410035644373836537 18714052807526733280377403)
    ·
      refine ⟨28071079211290099920566105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18714052807526733280377403 28071079211290099920566105)
      ·
        refine ⟨21053309408467574940424579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28071079211290099920566105 21053309408467574940424579)
        ·
          refine ⟨31579964112701362410636869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21053309408467574940424579 31579964112701362410636869)
          ·
            refine ⟨5921243271131505451994413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31579964112701362410636869 5921243271131505451994413)
            ·
              refine ⟨2220466226674314544497905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5921243271131505451994413 2220466226674314544497905)
              ·
                refine ⟨1665349670005735908373429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2220466226674314544497905 1665349670005735908373429)
                ·
                  refine ⟨156126531563037741410009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1665349670005735908373429 156126531563037741410009)
                  ·
                    rfl

theorem cell23_2736498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_2736498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736498 prefixEnd_2736498 := by exact prefixLift 2736498
  have htrace : WordTrace (prefixWord ++ tailWord_2736498) baseStart_2736498 baseEnd_2736498 := by
    simpa [prefixWord, tailWord_2736498, baseEnd_2736498] using wordTrace_append hprefix tailTrace_2736498
  have hstable : (prefixWord ++ tailWord_2736498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736498).length < 2 ^ (prefixWord ++ tailWord_2736498).sum := by decide
  have hdescent : baseEnd_2736498 < baseStart_2736498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736601 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 1, 5]
def baseStart_2736601 : Nat := 118140960795 + 2736601 * 2 ^ 59
def prefixEnd_2736601 : Nat := 4983230072969 + 3 ^ 40 * 2736601 * 2
def baseEnd_2736601 : Nat := 468397224191584256567369

theorem tailTrace_2736601 : CollatzResearch.WordTrace tailWord_2736601 prefixEnd_2736601 468397224191584256567369 := by
  unfold tailWord_2736601
  simp only [CollatzResearch.WordTrace]
  refine ⟨99812038358769426086345657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66541358905846284057563771 99812038358769426086345657)
  ·
    refine ⟨74859028769077069564759243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99812038358769426086345657 74859028769077069564759243)
    ·
      refine ⟨112288543153615604347138865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74859028769077069564759243 112288543153615604347138865)
      ·
        refine ⟨84216407365211703260354149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112288543153615604347138865 84216407365211703260354149)
        ·
          refine ⟨15790576380977194361316403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84216407365211703260354149 15790576380977194361316403)
          ·
            refine ⟨23685864571465791541974605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15790576380977194361316403 23685864571465791541974605)
            ·
              refine ⟨8882199214299671828240477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23685864571465791541974605 8882199214299671828240477)
              ·
                refine ⟨3330824705362376935590179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8882199214299671828240477 3330824705362376935590179)
                ·
                  refine ⟨4996237058043565403385269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330824705362376935590179 4996237058043565403385269)
                  ·
                    refine ⟨468397224191584256567369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4996237058043565403385269 468397224191584256567369)
                    ·
                      rfl

theorem cell23_2736601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 5].length) (baseStart_2736601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736601 prefixEnd_2736601 := by exact prefixLift 2736601
  have htrace : WordTrace (prefixWord ++ tailWord_2736601) baseStart_2736601 baseEnd_2736601 := by
    simpa [prefixWord, tailWord_2736601, baseEnd_2736601] using wordTrace_append hprefix tailTrace_2736601
  have hstable : (prefixWord ++ tailWord_2736601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736601).length < 2 ^ (prefixWord ++ tailWord_2736601).sum := by decide
  have hdescent : baseEnd_2736601 < baseStart_2736601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736615 : List Nat := [1, 1, 5, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_2736615 : Nat := 118140960795 + 2736615 * 2 ^ 59
def prefixEnd_2736615 : Nat := 4983230072969 + 3 ^ 40 * 2736615 * 2
def baseEnd_2736615 : Nat := 1405198861303915714927043

theorem tailTrace_2736615 : CollatzResearch.WordTrace tailWord_2736615 prefixEnd_2736615 1405198861303915714927043 := by
  unfold tailWord_2736615
  simp only [CollatzResearch.WordTrace]
  refine ⟨99812548980718706477355299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66541699320479137651570199 99812548980718706477355299)
  ·
    refine ⟨149718823471078059716032949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99812548980718706477355299 149718823471078059716032949)
    ·
      refine ⟨14036139700413568098378089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149718823471078059716032949 14036139700413568098378089)
      ·
        refine ⟨10527104775310176073783567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14036139700413568098378089 10527104775310176073783567)
        ·
          refine ⟨15790657162965264110675351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10527104775310176073783567 15790657162965264110675351)
          ·
            refine ⟨23685985744447896166013027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15790657162965264110675351 23685985744447896166013027)
            ·
              refine ⟨35528978616671844249019541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23685985744447896166013027 35528978616671844249019541)
              ·
                refine ⟨1665420872656492699172791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35528978616671844249019541 1665420872656492699172791)
                ·
                  refine ⟨2498131308984739048759187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665420872656492699172791 2498131308984739048759187)
                  ·
                    refine ⟨3747196963477108573138781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2498131308984739048759187 3747196963477108573138781)
                    ·
                      refine ⟨1405198861303915714927043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3747196963477108573138781 1405198861303915714927043)
                      ·
                        rfl

theorem cell23_2736615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_2736615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736615 prefixEnd_2736615 := by exact prefixLift 2736615
  have htrace : WordTrace (prefixWord ++ tailWord_2736615) baseStart_2736615 baseEnd_2736615 := by
    simpa [prefixWord, tailWord_2736615, baseEnd_2736615] using wordTrace_append hprefix tailTrace_2736615
  have hstable : (prefixWord ++ tailWord_2736615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736615).length < 2 ^ (prefixWord ++ tailWord_2736615).sum := by decide
  have hdescent : baseEnd_2736615 < baseStart_2736615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736682 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_2736682 : Nat := 118140960795 + 2736682 * 2 ^ 59
def prefixEnd_2736682 : Nat := 4983230072969 + 3 ^ 40 * 2736682 * 2
def baseEnd_2736682 : Nat := 468411088169255650929745

theorem tailTrace_2736682 : CollatzResearch.WordTrace tailWord_2736682 prefixEnd_2736682 468411088169255650929745 := by
  unfold tailWord_2736682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24953748167868994230011075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66543328447650651280029533 24953748167868994230011075)
  ·
    refine ⟨37430622251803491345016613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24953748167868994230011075 37430622251803491345016613)
    ·
      refine ⟨7018241672213154627190615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37430622251803491345016613 7018241672213154627190615)
      ·
        refine ⟨10527362508319731940785923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7018241672213154627190615 10527362508319731940785923)
        ·
          refine ⟨15791043762479597911178885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10527362508319731940785923 15791043762479597911178885)
          ·
            refine ⟨2960820705464924608346041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15791043762479597911178885 2960820705464924608346041)
            ·
              refine ⟨2220615529098693456259531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2960820705464924608346041 2220615529098693456259531)
              ·
                refine ⟨3330923293648040184389297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220615529098693456259531 3330923293648040184389297)
                ·
                  refine ⟨2498192470236030138291973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3330923293648040184389297 2498192470236030138291973)
                  ·
                    refine ⟨468411088169255650929745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2498192470236030138291973 468411088169255650929745)
                    ·
                      rfl

theorem cell23_2736682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_2736682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736682 prefixEnd_2736682 := by exact prefixLift 2736682
  have htrace : WordTrace (prefixWord ++ tailWord_2736682) baseStart_2736682 baseEnd_2736682 := by
    simpa [prefixWord, tailWord_2736682, baseEnd_2736682] using wordTrace_append hprefix tailTrace_2736682
  have hstable : (prefixWord ++ tailWord_2736682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736682).length < 2 ^ (prefixWord ++ tailWord_2736682).sum := by decide
  have hdescent : baseEnd_2736682 < baseStart_2736682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736692 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2736692 : Nat := 118140960795 + 2736692 * 2 ^ 59
def prefixEnd_2736692 : Nat := 4983230072969 + 3 ^ 40 * 2736692 * 2
def baseEnd_2736692 : Nat := 1405238399314311913664189

theorem tailTrace_2736692 : CollatzResearch.WordTrace tailWord_2736692 prefixEnd_2736692 1405238399314311913664189 := by
  unfold tailWord_2736692
  simp only [CollatzResearch.WordTrace]
  refine ⟨49907678700719874313954165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66543571600959832418605553 49907678700719874313954165)
  ·
    refine ⟨4678844878192488216933203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49907678700719874313954165 4678844878192488216933203)
    ·
      refine ⟨7018267317288732325399805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4678844878192488216933203 7018267317288732325399805)
      ·
        refine ⟨2631850243983274622024927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7018267317288732325399805 2631850243983274622024927)
        ·
          refine ⟨3947775365974911933037391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2631850243983274622024927 3947775365974911933037391)
          ·
            refine ⟨5921663048962367899556087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947775365974911933037391 5921663048962367899556087)
            ·
              refine ⟨8882494573443551849334131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5921663048962367899556087 8882494573443551849334131)
              ·
                refine ⟨13323741860165327774001197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8882494573443551849334131 13323741860165327774001197)
                ·
                  refine ⟨4996403197561997915250449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13323741860165327774001197 4996403197561997915250449)
                  ·
                    refine ⟨3747302398171498436437837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4996403197561997915250449 3747302398171498436437837)
                    ·
                      refine ⟨1405238399314311913664189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3747302398171498436437837 1405238399314311913664189)
                      ·
                        rfl

theorem cell23_2736692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2736692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736692 prefixEnd_2736692 := by exact prefixLift 2736692
  have htrace : WordTrace (prefixWord ++ tailWord_2736692) baseStart_2736692 baseEnd_2736692 := by
    simpa [prefixWord, tailWord_2736692, baseEnd_2736692] using wordTrace_append hprefix tailTrace_2736692
  have hstable : (prefixWord ++ tailWord_2736692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736692).length < 2 ^ (prefixWord ++ tailWord_2736692).sum := by decide
  have hdescent : baseEnd_2736692 < baseStart_2736692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736768 : List Nat := [2, 1, 1, 2, 1, 5, 1, 5, 5]
def baseStart_2736768 : Nat := 118140960795 + 2736768 * 2 ^ 59
def prefixEnd_2736768 : Nat := 4983230072969 + 3 ^ 40 * 2736768 * 2
def baseEnd_2736768 : Nat := 156141935982672624034871

theorem tailTrace_2736768 : CollatzResearch.WordTrace tailWord_2736768 prefixEnd_2736768 156141935982672624034871 := by
  unfold tailWord_2736768
  simp only [CollatzResearch.WordTrace]
  refine ⟨49909064674582206803837479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66545419566109609071783305 49909064674582206803837479)
  ·
    refine ⟨74863597011873310205756219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49909064674582206803837479 74863597011873310205756219)
    ·
      refine ⟨112295395517809965308634329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74863597011873310205756219 112295395517809965308634329)
      ·
        refine ⟨84221546638357473981475747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112295395517809965308634329 84221546638357473981475747)
        ·
          refine ⟨126332319957536210972213621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84221546638357473981475747 126332319957536210972213621)
          ·
            refine ⟨11843654996019019778645027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126332319957536210972213621 11843654996019019778645027)
            ·
              refine ⟨17765482494028529667967541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11843654996019019778645027 17765482494028529667967541)
              ·
                refine ⟨1665513983815174656371957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17765482494028529667967541 1665513983815174656371957)
                ·
                  refine ⟨156141935982672624034871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1665513983815174656371957 156141935982672624034871)
                  ·
                    rfl

theorem cell23_2736768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 5].length) (baseStart_2736768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736768 prefixEnd_2736768 := by exact prefixLift 2736768
  have htrace : WordTrace (prefixWord ++ tailWord_2736768) baseStart_2736768 baseEnd_2736768 := by
    simpa [prefixWord, tailWord_2736768, baseEnd_2736768] using wordTrace_append hprefix tailTrace_2736768
  have hstable : (prefixWord ++ tailWord_2736768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736768).length < 2 ^ (prefixWord ++ tailWord_2736768).sum := by decide
  have hdescent : baseEnd_2736768 < baseStart_2736768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736791 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2736791 : Nat := 118140960795 + 2736791 * 2 ^ 59
def prefixEnd_2736791 : Nat := 4983230072969 + 3 ^ 40 * 2736791 * 2
def baseEnd_2736791 : Nat := 1405289233899107026326233

theorem tailTrace_2736791 : CollatzResearch.WordTrace tailWord_2736791 prefixEnd_2736791 1405289233899107026326233 := by
  unfold tailWord_2736791
  simp only [CollatzResearch.WordTrace]
  refine ⟨99818968228081088535762227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66545978818720725690508151 99818968228081088535762227)
  ·
    refine ⟨149728452342121632803643341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99818968228081088535762227 149728452342121632803643341)
    ·
      refine ⟨56148169628295612301366253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149728452342121632803643341 56148169628295612301366253)
      ·
        refine ⟨21055563610610854613012345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56148169628295612301366253 21055563610610854613012345)
        ·
          refine ⟨15791672707958140959759259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21055563610610854613012345 15791672707958140959759259)
          ·
            refine ⟨23687509061937211439638889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15791672707958140959759259 23687509061937211439638889)
            ·
              refine ⟨17765631796452908579729167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23687509061937211439638889 17765631796452908579729167)
              ·
                refine ⟨26648447694679362869593751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17765631796452908579729167 26648447694679362869593751)
                ·
                  refine ⟨39972671542019044304390627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26648447694679362869593751 39972671542019044304390627)
                  ·
                    refine ⟨59959007313028566456585941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39972671542019044304390627 59959007313028566456585941)
                    ·
                      refine ⟨1405289233899107026326233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59959007313028566456585941 1405289233899107026326233)
                      ·
                        rfl

theorem cell23_2736791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2736791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736791 prefixEnd_2736791 := by exact prefixLift 2736791
  have htrace : WordTrace (prefixWord ++ tailWord_2736791) baseStart_2736791 baseEnd_2736791 := by
    simpa [prefixWord, tailWord_2736791, baseEnd_2736791] using wordTrace_append hprefix tailTrace_2736791
  have hstable : (prefixWord ++ tailWord_2736791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736791).length < 2 ^ (prefixWord ++ tailWord_2736791).sum := by decide
  have hdescent : baseEnd_2736791 < baseStart_2736791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736798 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2736798 : Nat := 118140960795 + 2736798 * 2 ^ 59
def prefixEnd_2736798 : Nat := 4983230072969 + 3 ^ 40 * 2736798 * 2
def baseEnd_2736798 : Nat := 468430942754562832979567

theorem tailTrace_2736798 : CollatzResearch.WordTrace tailWord_2736798 prefixEnd_2736798 468430942754562832979567 := by
  unfold tailWord_2736798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12477402942381966091408381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66546149026037152487511365 12477402942381966091408381)
  ·
    refine ⟨4679026103393237284278143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12477402942381966091408381 4679026103393237284278143)
    ·
      refine ⟨7018539155089855926417215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4679026103393237284278143 7018539155089855926417215)
      ·
        refine ⟨10527808732634783889625823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7018539155089855926417215 10527808732634783889625823)
        ·
          refine ⟨15791713098952175834438735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10527808732634783889625823 15791713098952175834438735)
          ·
            refine ⟨23687569648428263751658103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15791713098952175834438735 23687569648428263751658103)
            ·
              refine ⟨35531354472642395627487155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23687569648428263751658103 35531354472642395627487155)
              ·
                refine ⟨53297031708963593441230733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35531354472642395627487155 53297031708963593441230733)
                ·
                  refine ⟨19986386890861347540461525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53297031708963593441230733 19986386890861347540461525)
                  ·
                    refine ⟨468430942754562832979567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19986386890861347540461525 468430942754562832979567)
                    ·
                      rfl

theorem cell23_2736798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2736798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736798 prefixEnd_2736798 := by exact prefixLift 2736798
  have htrace : WordTrace (prefixWord ++ tailWord_2736798) baseStart_2736798 baseEnd_2736798 := by
    simpa [prefixWord, tailWord_2736798, baseEnd_2736798] using wordTrace_append hprefix tailTrace_2736798
  have hstable : (prefixWord ++ tailWord_2736798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736798).length < 2 ^ (prefixWord ++ tailWord_2736798).sum := by decide
  have hdescent : baseEnd_2736798 < baseStart_2736798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736818 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_2736818 : Nat := 118140960795 + 2736818 * 2 ^ 59
def prefixEnd_2736818 : Nat := 4983230072969 + 3 ^ 40 * 2736818 * 2
def baseEnd_2736818 : Nat := 1405303097876778420688609

theorem tailTrace_2736818 : CollatzResearch.WordTrace tailWord_2736818 prefixEnd_2736818 1405303097876778420688609 := by
  unfold tailWord_2736818
  simp only [CollatzResearch.WordTrace]
  refine ⟨24954988249745818036748777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66546635332655514764663405 24954988249745818036748777)
  ·
    refine ⟨18716241187309363527561583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24954988249745818036748777 18716241187309363527561583)
    ·
      refine ⟨28074361780964045291342375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18716241187309363527561583 28074361780964045291342375)
      ·
        refine ⟨42111542671446067937013563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28074361780964045291342375 42111542671446067937013563)
        ·
          refine ⟨63167314007169101905520345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42111542671446067937013563 63167314007169101905520345)
          ·
            refine ⟨47375485505376826429140259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63167314007169101905520345 47375485505376826429140259)
            ·
              refine ⟨71063228258065239643710389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47375485505376826429140259 71063228258065239643710389)
              ·
                refine ⟨6662177649193616216597849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71063228258065239643710389 6662177649193616216597849)
                ·
                  refine ⟨4996633236895212162448387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6662177649193616216597849 4996633236895212162448387)
                  ·
                    refine ⟨7494949855342818243672581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4996633236895212162448387 7494949855342818243672581)
                    ·
                      refine ⟨1405303097876778420688609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7494949855342818243672581 1405303097876778420688609)
                      ·
                        rfl

theorem cell23_2736818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_2736818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736818 prefixEnd_2736818 := by exact prefixLift 2736818
  have htrace : WordTrace (prefixWord ++ tailWord_2736818) baseStart_2736818 baseEnd_2736818 := by
    simpa [prefixWord, tailWord_2736818, baseEnd_2736818] using wordTrace_append hprefix tailTrace_2736818
  have hstable : (prefixWord ++ tailWord_2736818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736818).length < 2 ^ (prefixWord ++ tailWord_2736818).sum := by decide
  have hdescent : baseEnd_2736818 < baseStart_2736818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736858 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 6]
def baseStart_2736858 : Nat := 118140960795 + 2736858 * 2 ^ 59
def prefixEnd_2736858 : Nat := 4983230072969 + 3 ^ 40 * 2736858 * 2
def baseEnd_2736858 : Nat := 156147070789217584909825

theorem tailTrace_2736858 : CollatzResearch.WordTrace tailWord_2736858 prefixEnd_2736858 156147070789217584909825 := by
  unfold tailWord_2736858
  simp only [CollatzResearch.WordTrace]
  refine ⟨24955352979709589744612807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66547607945892239318967485 24955352979709589744612807)
  ·
    refine ⟨37433029469564384616919211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24955352979709589744612807 37433029469564384616919211)
    ·
      refine ⟨56149544204346576925378817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37433029469564384616919211 56149544204346576925378817)
      ·
        refine ⟨42112158153259932694034113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56149544204346576925378817 42112158153259932694034113)
        ·
          refine ⟨31584118614944949520525585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42112158153259932694034113 31584118614944949520525585)
          ·
            refine ⟨23688088961208712140394189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31584118614944949520525585 23688088961208712140394189)
            ·
              refine ⟨8883033360453267052647821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23688088961208712140394189 8883033360453267052647821)
              ·
                refine ⟨3331137510169975144742933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8883033360453267052647821 3331137510169975144742933)
                ·
                  refine ⟨156147070789217584909825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3331137510169975144742933 156147070789217584909825)
                  ·
                    rfl

theorem cell23_2736858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_2736858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736858 prefixEnd_2736858 := by exact prefixLift 2736858
  have htrace : WordTrace (prefixWord ++ tailWord_2736858) baseStart_2736858 baseEnd_2736858 := by
    simpa [prefixWord, tailWord_2736858, baseEnd_2736858] using wordTrace_append hprefix tailTrace_2736858
  have hstable : (prefixWord ++ tailWord_2736858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736858).length < 2 ^ (prefixWord ++ tailWord_2736858).sum := by decide
  have hdescent : baseEnd_2736858 < baseStart_2736858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736872 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_2736872 : Nat := 118140960795 + 2736872 * 2 ^ 59
def prefixEnd_2736872 : Nat := 4983230072969 + 3 ^ 40 * 2736872 * 2
def baseEnd_2736872 : Nat := 1405330825832121209413361

theorem tailTrace_2736872 : CollatzResearch.WordTrace tailWord_2736872 prefixEnd_2736872 1405330825832121209413361 := by
  unfold tailWord_2736872
  simp only [CollatzResearch.WordTrace]
  refine ⟨49910961270393819684730435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66547948360525092912973913 49910961270393819684730435)
  ·
    refine ⟨74866441905590729527095653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49910961270393819684730435 74866441905590729527095653)
    ·
      refine ⟨14037457857298261786330435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74866441905590729527095653 14037457857298261786330435)
      ·
        refine ⟨21056186785947392679495653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14037457857298261786330435 21056186785947392679495653)
        ·
          refine ⟨3948035022365136127405435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21056186785947392679495653 3948035022365136127405435)
          ·
            refine ⟨5922052533547704191108153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948035022365136127405435 5922052533547704191108153)
            ·
              refine ⟨4441539400160778143331115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922052533547704191108153 4441539400160778143331115)
              ·
                refine ⟨6662309100241167214996673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441539400160778143331115 6662309100241167214996673)
                ·
                  refine ⟨4996731825180875411247505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6662309100241167214996673 4996731825180875411247505)
                  ·
                    refine ⟨3747548868885656558435629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4996731825180875411247505 3747548868885656558435629)
                    ·
                      refine ⟨1405330825832121209413361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3747548868885656558435629 1405330825832121209413361)
                      ·
                        rfl

theorem cell23_2736872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_2736872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736872 prefixEnd_2736872 := by exact prefixLift 2736872
  have htrace : WordTrace (prefixWord ++ tailWord_2736872) baseStart_2736872 baseEnd_2736872 := by
    simpa [prefixWord, tailWord_2736872, baseEnd_2736872] using wordTrace_append hprefix tailTrace_2736872
  have hstable : (prefixWord ++ tailWord_2736872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736872).length < 2 ^ (prefixWord ++ tailWord_2736872).sum := by decide
  have hdescent : baseEnd_2736872 < baseStart_2736872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736959 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 3, 2, 2]
def baseStart_2736959 : Nat := 118140960795 + 2736959 * 2 ^ 59
def prefixEnd_2736959 : Nat := 4983230072969 + 3 ^ 40 * 2736959 * 2
def baseEnd_2736959 : Nat := 1405375498649062369025461

theorem tailTrace_2736959 : CollatzResearch.WordTrace tailWord_2736959 prefixEnd_2736959 1405375498649062369025461 := by
  unfold tailWord_2736959
  simp only [CollatzResearch.WordTrace]
  refine ⟨99825095691472453227877931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66550063794314968818585287 99825095691472453227877931)
  ·
    refine ⟨149737643537208679841816897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99825095691472453227877931 149737643537208679841816897)
    ·
      refine ⟨112303232652906509881362673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149737643537208679841816897 112303232652906509881362673)
      ·
        refine ⟨84227424489679882411022005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112303232652906509881362673 84227424489679882411022005)
        ·
          refine ⟨7896321045907488976033313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84227424489679882411022005 7896321045907488976033313)
          ·
            refine ⟨5922240784430616732024985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7896321045907488976033313 5922240784430616732024985)
            ·
              refine ⟨4441680588322962549018739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922240784430616732024985 4441680588322962549018739)
              ·
                refine ⟨6662520882484443823528109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441680588322962549018739 6662520882484443823528109)
                ·
                  refine ⟨2498445330931666433823041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6662520882484443823528109 2498445330931666433823041)
                  ·
                    refine ⟨1873833998198749825367281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2498445330931666433823041 1873833998198749825367281)
                    ·
                      refine ⟨1405375498649062369025461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1873833998198749825367281 1405375498649062369025461)
                      ·
                        rfl

theorem cell23_2736959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_2736959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736959 prefixEnd_2736959 := by exact prefixLift 2736959
  have htrace : WordTrace (prefixWord ++ tailWord_2736959) baseStart_2736959 baseEnd_2736959 := by
    simpa [prefixWord, tailWord_2736959, baseEnd_2736959] using wordTrace_append hprefix tailTrace_2736959
  have hstable : (prefixWord ++ tailWord_2736959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736959).length < 2 ^ (prefixWord ++ tailWord_2736959).sum := by decide
  have hdescent : baseEnd_2736959 < baseStart_2736959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2736972 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2736972 : Nat := 118140960795 + 2736972 * 2 ^ 59
def prefixEnd_2736972 : Nat := 4983230072969 + 3 ^ 40 * 2736972 * 2
def baseEnd_2736972 : Nat := 1405382173897570818162901

theorem tailTrace_2736972 : CollatzResearch.WordTrace tailWord_2736972 prefixEnd_2736972 1405382173897570818162901 := by
  unfold tailWord_2736972
  simp only [CollatzResearch.WordTrace]
  refine ⟨49912784920212678224050585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66550379893616904298734113 49912784920212678224050585)
  ·
    refine ⟨37434588690159508668037939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49912784920212678224050585 37434588690159508668037939)
    ·
      refine ⟨56151883035239263002056909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37434588690159508668037939 56151883035239263002056909)
      ·
        refine ⟨21056956138214723625771341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56151883035239263002056909 21056956138214723625771341)
        ·
          refine ⟨7896358551830521359664253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21056956138214723625771341 7896358551830521359664253)
          ·
            refine ⟨2961134456936445509874095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7896358551830521359664253 2961134456936445509874095)
            ·
              refine ⟨4441701685404668264811143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961134456936445509874095 4441701685404668264811143)
              ·
                refine ⟨6662552528107002397216715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441701685404668264811143 6662552528107002397216715)
                ·
                  refine ⟨9993828792160503595825073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6662552528107002397216715 9993828792160503595825073)
                  ·
                    refine ⟨7495371594120377696868805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9993828792160503595825073 7495371594120377696868805)
                    ·
                      refine ⟨1405382173897570818162901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7495371594120377696868805 1405382173897570818162901)
                      ·
                        rfl

theorem cell23_2736972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2736972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2736972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2736972 prefixEnd_2736972 := by exact prefixLift 2736972
  have htrace : WordTrace (prefixWord ++ tailWord_2736972) baseStart_2736972 baseEnd_2736972 := by
    simpa [prefixWord, tailWord_2736972, baseEnd_2736972] using wordTrace_append hprefix tailTrace_2736972
  have hstable : (prefixWord ++ tailWord_2736972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2736972).length < 2 ^ (prefixWord ++ tailWord_2736972).sum := by decide
  have hdescent : baseEnd_2736972 < baseStart_2736972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2736972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737008 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 4, 6]
def baseStart_2737008 : Nat := 118140960795 + 2737008 * 2 ^ 59
def prefixEnd_2737008 : Nat := 4983230072969 + 3 ^ 40 * 2737008 * 2
def baseEnd_2737008 : Nat := 468466886400377559104245

theorem tailTrace_2737008 : CollatzResearch.WordTrace tailWord_2737008 prefixEnd_2737008 468466886400377559104245 := by
  unfold tailWord_2737008
  simp only [CollatzResearch.WordTrace]
  refine ⟨49913441434147467298205839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66551255245529956397607785 49913441434147467298205839)
  ·
    refine ⟨74870162151221200947308759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49913441434147467298205839 74870162151221200947308759)
    ·
      refine ⟨112305243226831801420963139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74870162151221200947308759 112305243226831801420963139)
      ·
        refine ⟨168457864840247702131444709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112305243226831801420963139 168457864840247702131444709)
        ·
          refine ⟨31585849657546444149645883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168457864840247702131444709 31585849657546444149645883)
          ·
            refine ⟨47378774486319666224468825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31585849657546444149645883 47378774486319666224468825)
            ·
              refine ⟨35534080864739749668351619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47378774486319666224468825 35534080864739749668351619)
              ·
                refine ⟨53301121297109624502527429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35534080864739749668351619 53301121297109624502527429)
                ·
                  refine ⟨9993960243208054594223893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53301121297109624502527429 9993960243208054594223893)
                  ·
                    refine ⟨468466886400377559104245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9993960243208054594223893 468466886400377559104245)
                    ·
                      rfl

theorem cell23_2737008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_2737008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737008 prefixEnd_2737008 := by exact prefixLift 2737008
  have htrace : WordTrace (prefixWord ++ tailWord_2737008) baseStart_2737008 baseEnd_2737008 := by
    simpa [prefixWord, tailWord_2737008, baseEnd_2737008] using wordTrace_append hprefix tailTrace_2737008
  have hstable : (prefixWord ++ tailWord_2737008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737008).length < 2 ^ (prefixWord ++ tailWord_2737008).sum := by decide
  have hdescent : baseEnd_2737008 < baseStart_2737008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737018 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_2737018 : Nat := 118140960795 + 2737018 * 2 ^ 59
def prefixEnd_2737018 : Nat := 4983230072969 + 3 ^ 40 * 2737018 * 2
def baseEnd_2737018 : Nat := 1405405794007677638187689

theorem tailTrace_2737018 : CollatzResearch.WordTrace tailWord_2737018 prefixEnd_2737018 1405405794007677638187689 := by
  unfold tailWord_2737018
  simp only [CollatzResearch.WordTrace]
  refine ⟨24956811899564676576068927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66551498398839137536183805 24956811899564676576068927)
  ·
    refine ⟨37435217849347014864103391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24956811899564676576068927 37435217849347014864103391)
    ·
      refine ⟨56152826774020522296155087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37435217849347014864103391 56152826774020522296155087)
      ·
        refine ⟨84229240161030783444232631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56152826774020522296155087 84229240161030783444232631)
        ·
          refine ⟨126343860241546175166348947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84229240161030783444232631 126343860241546175166348947)
          ·
            refine ⟨189515790362319262749523421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126343860241546175166348947 189515790362319262749523421)
            ·
              refine ⟨71068421385869723531071283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189515790362319262749523421 71068421385869723531071283)
              ·
                refine ⟨106602632078804585296606925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71068421385869723531071283 106602632078804585296606925)
                ·
                  refine ⟨39975987029551719486227597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106602632078804585296606925 39975987029551719486227597)
                  ·
                    refine ⟨14990995136081894807335349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39975987029551719486227597 14990995136081894807335349)
                    ·
                      refine ⟨1405405794007677638187689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14990995136081894807335349 1405405794007677638187689)
                      ·
                        rfl

theorem cell23_2737018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_2737018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737018 prefixEnd_2737018 := by exact prefixLift 2737018
  have htrace : WordTrace (prefixWord ++ tailWord_2737018) baseStart_2737018 baseEnd_2737018 := by
    simpa [prefixWord, tailWord_2737018, baseEnd_2737018] using wordTrace_append hprefix tailTrace_2737018
  have hstable : (prefixWord ++ tailWord_2737018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737018).length < 2 ^ (prefixWord ++ tailWord_2737018).sum := by decide
  have hdescent : baseEnd_2737018 < baseStart_2737018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737065 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 3]
def baseStart_2737065 : Nat := 118140960795 + 2737065 * 2 ^ 59
def prefixEnd_2737065 : Nat := 4983230072969 + 3 ^ 40 * 2737065 * 2
def baseEnd_2737065 : Nat := 1405429927598438954299973

theorem tailTrace_2737065 : CollatzResearch.WordTrace tailWord_2737065 prefixEnd_2737065 1405429927598438954299973 := by
  unfold tailWord_2737065
  simp only [CollatzResearch.WordTrace]
  refine ⟨99828961829088433331236649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66552641219392288887491099 99828961829088433331236649)
  ·
    refine ⟨74871721371816324998427487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99828961829088433331236649 74871721371816324998427487)
    ·
      refine ⟨112307582057724487497641231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74871721371816324998427487 112307582057724487497641231)
      ·
        refine ⟨168461373086586731246461847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112307582057724487497641231 168461373086586731246461847)
        ·
          refine ⟨252692059629880096869692771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168461373086586731246461847 252692059629880096869692771)
          ·
            refine ⟨379038089444820145304539157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252692059629880096869692771 379038089444820145304539157)
            ·
              refine ⟨17767410442725944311150273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 379038089444820145304539157 17767410442725944311150273)
              ·
                refine ⟨13325557832044458233362705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17767410442725944311150273 13325557832044458233362705)
                ·
                  refine ⟨9994168374033343675022029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13325557832044458233362705 9994168374033343675022029)
                  ·
                    refine ⟨3747813140262503878133261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9994168374033343675022029 3747813140262503878133261)
                    ·
                      refine ⟨1405429927598438954299973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3747813140262503878133261 1405429927598438954299973)
                      ·
                        rfl

theorem cell23_2737065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_2737065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737065 prefixEnd_2737065 := by exact prefixLift 2737065
  have htrace : WordTrace (prefixWord ++ tailWord_2737065) baseStart_2737065 baseEnd_2737065 := by
    simpa [prefixWord, tailWord_2737065, baseEnd_2737065] using wordTrace_append hprefix tailTrace_2737065
  have hstable : (prefixWord ++ tailWord_2737065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737065).length < 2 ^ (prefixWord ++ tailWord_2737065).sum := by decide
  have hdescent : baseEnd_2737065 < baseStart_2737065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737102 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_2737102 : Nat := 118140960795 + 2737102 * 2 ^ 59
def prefixEnd_2737102 : Nat := 4983230072969 + 3 ^ 40 * 2737102 * 2
def baseEnd_2737102 : Nat := 468482975460885103179101

theorem tailTrace_2737102 : CollatzResearch.WordTrace tailWord_2737102 prefixEnd_2737102 468482975460885103179101 := by
  unfold tailWord_2737102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12478788916244298581291695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66553540886636259100222373 12478788916244298581291695)
  ·
    refine ⟨18718183374366447871937543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12478788916244298581291695 18718183374366447871937543)
    ·
      refine ⟨28077275061549671807906315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18718183374366447871937543 28077275061549671807906315)
      ·
        refine ⟨42115912592324507711859473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28077275061549671807906315 42115912592324507711859473)
        ·
          refine ⟨31586934444243380783894605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42115912592324507711859473 31586934444243380783894605)
          ·
            refine ⟨11845100416591267793960477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31586934444243380783894605 11845100416591267793960477)
            ·
              refine ⟨4441912656221725422735179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11845100416591267793960477 4441912656221725422735179)
              ·
                refine ⟨6662868984332588134102769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4441912656221725422735179 6662868984332588134102769)
                ·
                  refine ⟨4997151738249441100577077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6662868984332588134102769 4997151738249441100577077)
                  ·
                    refine ⟨468482975460885103179101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4997151738249441100577077 468482975460885103179101)
                    ·
                      rfl

theorem cell23_2737102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_2737102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737102 prefixEnd_2737102 := by exact prefixLift 2737102
  have htrace : WordTrace (prefixWord ++ tailWord_2737102) baseStart_2737102 baseEnd_2737102 := by
    simpa [prefixWord, tailWord_2737102, baseEnd_2737102] using wordTrace_append hprefix tailTrace_2737102
  have hstable : (prefixWord ++ tailWord_2737102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737102).length < 2 ^ (prefixWord ++ tailWord_2737102).sum := by decide
  have hdescent : baseEnd_2737102 < baseStart_2737102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737105 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_2737105 : Nat := 118140960795 + 2737105 * 2 ^ 59
def prefixEnd_2737105 : Nat := 4983230072969 + 3 ^ 40 * 2737105 * 2
def baseEnd_2737105 : Nat := 1405450466824618797799789

theorem tailTrace_2737105 : CollatzResearch.WordTrace tailWord_2737105 prefixEnd_2737105 1405450466824618797799789 := by
  unfold tailWord_2737105
  simp only [CollatzResearch.WordTrace]
  refine ⟨99830420748943520162692769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66553613832629013441795179 99830420748943520162692769)
  ·
    refine ⟨74872815561707640122019577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99830420748943520162692769 74872815561707640122019577)
    ·
      refine ⟨56154611671280730091514683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74872815561707640122019577 56154611671280730091514683)
      ·
        refine ⟨84231917506921095137272025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56154611671280730091514683 84231917506921095137272025)
        ·
          refine ⟨63173938130190821352954019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84231917506921095137272025 63173938130190821352954019)
          ·
            refine ⟨94760907195286232029431029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63173938130190821352954019 94760907195286232029431029)
            ·
              refine ⟨8883835049558084252759159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94760907195286232029431029 8883835049558084252759159)
              ·
                refine ⟨13325752574337126379138739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8883835049558084252759159 13325752574337126379138739)
                ·
                  refine ⟨19988628861505689568708109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13325752574337126379138739 19988628861505689568708109)
                  ·
                    refine ⟨7495735823064633588265541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19988628861505689568708109 7495735823064633588265541)
                    ·
                      refine ⟨1405450466824618797799789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7495735823064633588265541 1405450466824618797799789)
                      ·
                        rfl

theorem cell23_2737105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_2737105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737105 prefixEnd_2737105 := by exact prefixLift 2737105
  have htrace : WordTrace (prefixWord ++ tailWord_2737105) baseStart_2737105 baseEnd_2737105 := by
    simpa [prefixWord, tailWord_2737105, baseEnd_2737105] using wordTrace_append hprefix tailTrace_2737105
  have hstable : (prefixWord ++ tailWord_2737105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737105).length < 2 ^ (prefixWord ++ tailWord_2737105).sum := by decide
  have hdescent : baseEnd_2737105 < baseStart_2737105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737166 : List Nat := [4, 1, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_2737166 : Nat := 118140960795 + 2737166 * 2 ^ 59
def prefixEnd_2737166 : Nat := 4983230072969 + 3 ^ 40 * 2737166 * 2
def baseEnd_2737166 : Nat := 468493929714847686379003

theorem tailTrace_2737166 : CollatzResearch.WordTrace tailWord_2737166 prefixEnd_2737166 468493929714847686379003 := by
  unfold tailWord_2737166
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479080700215315947582919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66555097067815018387108901 12479080700215315947582919)
  ·
    refine ⟨18718621050322973921374379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12479080700215315947582919 18718621050322973921374379)
    ·
      refine ⟨28077931575484460882061569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18718621050322973921374379 28077931575484460882061569)
      ·
        refine ⟨21058448681613345661546177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28077931575484460882061569 21058448681613345661546177)
        ·
          refine ⟨15793836511210009246159633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21058448681613345661546177 15793836511210009246159633)
          ·
            refine ⟨11845377383407506934619725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15793836511210009246159633 11845377383407506934619725)
            ·
              refine ⟨4442016518777815100482397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11845377383407506934619725 4442016518777815100482397)
              ·
                refine ⟨1665756194541680662680899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4442016518777815100482397 1665756194541680662680899)
                ·
                  refine ⟨2498634291812520994021349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665756194541680662680899 2498634291812520994021349)
                  ·
                    refine ⟨468493929714847686379003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2498634291812520994021349 468493929714847686379003)
                    ·
                      rfl

theorem cell23_2737166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_2737166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737166 prefixEnd_2737166 := by exact prefixLift 2737166
  have htrace : WordTrace (prefixWord ++ tailWord_2737166) baseStart_2737166 baseEnd_2737166 := by
    simpa [prefixWord, tailWord_2737166, baseEnd_2737166] using wordTrace_append hprefix tailTrace_2737166
  have hstable : (prefixWord ++ tailWord_2737166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737166).length < 2 ^ (prefixWord ++ tailWord_2737166).sum := by decide
  have hdescent : baseEnd_2737166 < baseStart_2737166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737209 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 1, 5]
def baseStart_2737209 : Nat := 118140960795 + 2737209 * 2 ^ 59
def prefixEnd_2737209 : Nat := 4983230072969 + 3 ^ 40 * 2737209 * 2
def baseEnd_2737209 : Nat := 468501289604228796966437

theorem tailTrace_2737209 : CollatzResearch.WordTrace tailWord_2737209 prefixEnd_2737209 468501289604228796966437 := by
  unfold tailWord_2737209
  simp only [CollatzResearch.WordTrace]
  refine ⟨99834213940566745924478681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66556142627044497282985787 99834213940566745924478681)
  ·
    refine ⟨74875660455425059443359011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99834213940566745924478681 74875660455425059443359011)
    ·
      refine ⟨112313490683137589165038517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74875660455425059443359011 112313490683137589165038517)
      ·
        refine ⟨10529389751544148984222361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112313490683137589165038517 10529389751544148984222361)
        ·
          refine ⟨7897042313658111738166771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10529389751544148984222361 7897042313658111738166771)
          ·
            refine ⟨11845563470487167607250157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897042313658111738166771 11845563470487167607250157)
            ·
              refine ⟨4442086301432687852718809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11845563470487167607250157 4442086301432687852718809)
              ·
                refine ⟨3331564726074515889539107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4442086301432687852718809 3331564726074515889539107)
                ·
                  refine ⟨4997347089111773834308661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331564726074515889539107 4997347089111773834308661)
                  ·
                    refine ⟨468501289604228796966437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4997347089111773834308661 468501289604228796966437)
                    ·
                      rfl

theorem cell23_2737209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 5].length) (baseStart_2737209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737209 prefixEnd_2737209 := by exact prefixLift 2737209
  have htrace : WordTrace (prefixWord ++ tailWord_2737209) baseStart_2737209 baseEnd_2737209 := by
    simpa [prefixWord, tailWord_2737209, baseEnd_2737209] using wordTrace_append hprefix tailTrace_2737209
  have hstable : (prefixWord ++ tailWord_2737209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737209).length < 2 ^ (prefixWord ++ tailWord_2737209).sum := by decide
  have hdescent : baseEnd_2737209 < baseStart_2737209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737225 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_2737225 : Nat := 118140960795 + 2737225 * 2 ^ 59
def prefixEnd_2737225 : Nat := 4983230072969 + 3 ^ 40 * 2737225 * 2
def baseEnd_2737225 : Nat := 1405512084503158328299237

theorem tailTrace_2737225 : CollatzResearch.WordTrace tailWord_2737225 prefixEnd_2737225 1405512084503158328299237 := by
  unfold tailWord_2737225
  simp only [CollatzResearch.WordTrace]
  refine ⟨99834797508508780657061129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66556531672339187104707419 99834797508508780657061129)
  ·
    refine ⟨74876098131381585492795847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99834797508508780657061129 74876098131381585492795847)
    ·
      refine ⟨112314147197072378239193771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74876098131381585492795847 112314147197072378239193771)
      ·
        refine ⟨168471220795608567358790657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112314147197072378239193771 168471220795608567358790657)
        ·
          refine ⟨126353415596706425519092993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168471220795608567358790657 126353415596706425519092993)
          ·
            refine ⟨94765061697529819139319745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126353415596706425519092993 94765061697529819139319745)
            ·
              refine ⟨71073796273147364354489809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94765061697529819139319745 71073796273147364354489809)
              ·
                refine ⟨53305347204860523265867357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71073796273147364354489809 53305347204860523265867357)
                ·
                  refine ⟨19989505201822696224700259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53305347204860523265867357 19989505201822696224700259)
                  ·
                    refine ⟨29984257802734044337050389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19989505201822696224700259 29984257802734044337050389)
                    ·
                      refine ⟨1405512084503158328299237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29984257802734044337050389 1405512084503158328299237)
                      ·
                        rfl

theorem cell23_2737225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_2737225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737225 prefixEnd_2737225 := by exact prefixLift 2737225
  have htrace : WordTrace (prefixWord ++ tailWord_2737225) baseStart_2737225 baseEnd_2737225 := by
    simpa [prefixWord, tailWord_2737225, baseEnd_2737225] using wordTrace_append hprefix tailTrace_2737225
  have hstable : (prefixWord ++ tailWord_2737225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737225).length < 2 ^ (prefixWord ++ tailWord_2737225).sum := by decide
  have hdescent : baseEnd_2737225 < baseStart_2737225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737256 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 1, 6]
def baseStart_2737256 : Nat := 118140960795 + 2737256 * 2 ^ 59
def prefixEnd_2737256 : Nat := 4983230072969 + 3 ^ 40 * 2737256 * 2
def baseEnd_2737256 : Nat := 468509334134482569003865

theorem tailTrace_2737256 : CollatzResearch.WordTrace tailWord_2737256 prefixEnd_2737256 468509334134482569003865 := by
  unfold tailWord_2737256
  simp only [CollatzResearch.WordTrace]
  refine ⟨49917964085698236475719811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66557285447597648634293081 49917964085698236475719811)
  ·
    refine ⟨74876946128547354713579717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49917964085698236475719811 74876946128547354713579717)
    ·
      refine ⟨14039427399102629008796197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74876946128547354713579717 14039427399102629008796197)
      ·
        refine ⟨2632392637331742939149287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14039427399102629008796197 2632392637331742939149287)
        ·
          refine ⟨3948588955997614408723931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2632392637331742939149287 3948588955997614408723931)
          ·
            refine ⟨5922883433996421613085897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948588955997614408723931 5922883433996421613085897)
            ·
              refine ⟨4442162575497316209814423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922883433996421613085897 4442162575497316209814423)
              ·
                refine ⟨6663243863245974314721635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4442162575497316209814423 6663243863245974314721635)
                ·
                  refine ⟨9994865794868961472082453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6663243863245974314721635 9994865794868961472082453)
                  ·
                    refine ⟨468509334134482569003865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9994865794868961472082453 468509334134482569003865)
                    ·
                      rfl

theorem cell23_2737256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_2737256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737256 prefixEnd_2737256 := by exact prefixLift 2737256
  have htrace : WordTrace (prefixWord ++ tailWord_2737256) baseStart_2737256 baseEnd_2737256 := by
    simpa [prefixWord, tailWord_2737256, baseEnd_2737256] using wordTrace_append hprefix tailTrace_2737256
  have hstable : (prefixWord ++ tailWord_2737256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737256).length < 2 ^ (prefixWord ++ tailWord_2737256).sum := by decide
  have hdescent : baseEnd_2737256 < baseStart_2737256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737312 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 2, 6]
def baseStart_2737312 : Nat := 118140960795 + 2737312 * 2 ^ 59
def prefixEnd_2737312 : Nat := 4983230072969 + 3 ^ 40 * 2737312 * 2
def baseEnd_2737312 : Nat := 468518919106699829303779

theorem tailTrace_2737312 : CollatzResearch.WordTrace tailWord_2737312 prefixEnd_2737312 468518919106699829303779 := by
  unfold tailWord_2737312
  simp only [CollatzResearch.WordTrace]
  refine ⟨49918985329596797257739095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66558647106129063010318793 49918985329596797257739095)
  ·
    refine ⟨74878477994395195886608643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49918985329596797257739095 74878477994395195886608643)
    ·
      refine ⟨112317716991592793829912965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74878477994395195886608643 112317716991592793829912965)
      ·
        refine ⟨21059571935923648843108681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112317716991592793829912965 21059571935923648843108681)
        ·
          refine ⟨15794678951942736632331511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21059571935923648843108681 15794678951942736632331511)
          ·
            refine ⟨23692018427914104948497267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15794678951942736632331511 23692018427914104948497267)
            ·
              refine ⟨35538027641871157422745901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23692018427914104948497267 35538027641871157422745901)
              ·
                refine ⟨13326760365701684033529713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35538027641871157422745901 13326760365701684033529713)
                ·
                  refine ⟨9995070274276263025147285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13326760365701684033529713 9995070274276263025147285)
                  ·
                    refine ⟨468518919106699829303779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9995070274276263025147285 468518919106699829303779)
                    ·
                      rfl

theorem cell23_2737312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_2737312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737312 prefixEnd_2737312 := by exact prefixLift 2737312
  have htrace : WordTrace (prefixWord ++ tailWord_2737312) baseStart_2737312 baseEnd_2737312 := by
    simpa [prefixWord, tailWord_2737312, baseEnd_2737312] using wordTrace_append hprefix tailTrace_2737312
  have hstable : (prefixWord ++ tailWord_2737312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737312).length < 2 ^ (prefixWord ++ tailWord_2737312).sum := by decide
  have hdescent : baseEnd_2737312 < baseStart_2737312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737313 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_2737313 : Nat := 118140960795 + 2737313 * 2 ^ 59
def prefixEnd_2737313 : Nat := 4983230072969 + 3 ^ 40 * 2737313 * 2
def baseEnd_2737313 : Nat := 1405557270800753983998833

theorem tailTrace_2737313 : CollatzResearch.WordTrace tailWord_2737313 prefixEnd_2737313 1405557270800753983998833 := by
  unfold tailWord_2737313
  simp only [CollatzResearch.WordTrace]
  refine ⟨99838007132189971686264593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66558671421459981124176395 99838007132189971686264593)
  ·
    refine ⟨74878505349142478764698445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99838007132189971686264593 74878505349142478764698445)
    ·
      refine ⟨28079439505928429536761917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74878505349142478764698445 28079439505928429536761917)
      ·
        refine ⟨10529789814723161076285719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28079439505928429536761917 10529789814723161076285719)
        ·
          refine ⟨15794684722084741614428579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10529789814723161076285719 15794684722084741614428579)
          ·
            refine ⟨23692027083127112421642869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15794684722084741614428579 23692027083127112421642869)
            ·
              refine ⟨2221127539043166789529019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23692027083127112421642869 2221127539043166789529019)
              ·
                refine ⟨3331691308564750184293529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221127539043166789529019 3331691308564750184293529)
                ·
                  refine ⟨2498768481423562638220147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3331691308564750184293529 2498768481423562638220147)
                  ·
                    refine ⟨3748152722135343957330221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2498768481423562638220147 3748152722135343957330221)
                    ·
                      refine ⟨1405557270800753983998833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3748152722135343957330221 1405557270800753983998833)
                      ·
                        rfl

theorem cell23_2737313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_2737313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737313 prefixEnd_2737313 := by exact prefixLift 2737313
  have htrace : WordTrace (prefixWord ++ tailWord_2737313) baseStart_2737313 baseEnd_2737313 := by
    simpa [prefixWord, tailWord_2737313, baseEnd_2737313] using wordTrace_append hprefix tailTrace_2737313
  have hstable : (prefixWord ++ tailWord_2737313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737313).length < 2 ^ (prefixWord ++ tailWord_2737313).sum := by decide
  have hdescent : baseEnd_2737313 < baseStart_2737313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737364 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2737364 : Nat := 118140960795 + 2737364 * 2 ^ 59
def prefixEnd_2737364 : Nat := 4983230072969 + 3 ^ 40 * 2737364 * 2
def baseEnd_2737364 : Nat := 1405583458314133284461099

theorem tailTrace_2737364 : CollatzResearch.WordTrace tailWord_2737364 prefixEnd_2737364 1405583458314133284461099 := by
  unfold tailWord_2737364
  simp only [CollatzResearch.WordTrace]
  refine ⟨49919933627502603698185573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66559911503336804930914097 49919933627502603698185573)
  ·
    refine ⟨9359987555156738193409795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49919933627502603698185573 9359987555156738193409795)
    ·
      refine ⟨14039981332735107290114693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9359987555156738193409795 14039981332735107290114693)
      ·
        refine ⟨2632496499887832616896505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14039981332735107290114693 2632496499887832616896505)
        ·
          refine ⟨1974372374915874462672379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2632496499887832616896505 1974372374915874462672379)
          ·
            refine ⟨2961558562373811694008569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974372374915874462672379 2961558562373811694008569)
            ·
              refine ⟨2221168921780358770506427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2961558562373811694008569 2221168921780358770506427)
              ·
                refine ⟨3331753382670538155759641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221168921780358770506427 3331753382670538155759641)
                ·
                  refine ⟨2498815037002903616819731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3331753382670538155759641 2498815037002903616819731)
                  ·
                    refine ⟨3748222555504355425229597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2498815037002903616819731 3748222555504355425229597)
                    ·
                      refine ⟨1405583458314133284461099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3748222555504355425229597 1405583458314133284461099)
                      ·
                        rfl

theorem cell23_2737364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2737364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737364 prefixEnd_2737364 := by exact prefixLift 2737364
  have htrace : WordTrace (prefixWord ++ tailWord_2737364) baseStart_2737364 baseEnd_2737364 := by
    simpa [prefixWord, tailWord_2737364, baseEnd_2737364] using wordTrace_append hprefix tailTrace_2737364
  have hstable : (prefixWord ++ tailWord_2737364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737364).length < 2 ^ (prefixWord ++ tailWord_2737364).sum := by decide
  have hdescent : baseEnd_2737364 < baseStart_2737364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737406 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2737406 : Nat := 118140960795 + 2737406 * 2 ^ 59
def prefixEnd_2737406 : Nat := 4983230072969 + 3 ^ 40 * 2737406 * 2
def baseEnd_2737406 : Nat := 468535008167207373378635

theorem tailTrace_2737406 : CollatzResearch.WordTrace tailWord_2737406 prefixEnd_2737406 468535008167207373378635 := by
  unfold tailWord_2737406
  simp only [CollatzResearch.WordTrace]
  refine ⟨12480174890106631071175009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66560932747235365712933381 12480174890106631071175009)
  ·
    refine ⟨9360131167579973303381257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12480174890106631071175009 9360131167579973303381257)
    ·
      refine ⟨7020098375684979977535943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9360131167579973303381257 7020098375684979977535943)
      ·
        refine ⟨10530147563527469966303915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7020098375684979977535943 10530147563527469966303915)
        ·
          refine ⟨15795221345291204949455873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10530147563527469966303915 15795221345291204949455873)
          ·
            refine ⟨11846416008968403712091905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15795221345291204949455873 11846416008968403712091905)
            ·
              refine ⟨8884812006726302784068929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11846416008968403712091905 8884812006726302784068929)
              ·
                refine ⟨6663609005044727088051697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8884812006726302784068929 6663609005044727088051697)
                ·
                  refine ⟨4997706753783545316038773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6663609005044727088051697 4997706753783545316038773)
                  ·
                    refine ⟨468535008167207373378635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4997706753783545316038773 468535008167207373378635)
                    ·
                      rfl

theorem cell23_2737406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2737406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737406 prefixEnd_2737406 := by exact prefixLift 2737406
  have htrace : WordTrace (prefixWord ++ tailWord_2737406) baseStart_2737406 baseEnd_2737406 := by
    simpa [prefixWord, tailWord_2737406, baseEnd_2737406] using wordTrace_append hprefix tailTrace_2737406
  have hstable : (prefixWord ++ tailWord_2737406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737406).length < 2 ^ (prefixWord ++ tailWord_2737406).sum := by decide
  have hdescent : baseEnd_2737406 < baseStart_2737406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737429 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_2737429 : Nat := 118140960795 + 2737429 * 2 ^ 59
def prefixEnd_2737429 : Nat := 4983230072969 + 3 ^ 40 * 2737429 * 2
def baseEnd_2737429 : Nat := 1405616834556675530148299

theorem tailTrace_2737429 : CollatzResearch.WordTrace tailWord_2737429 prefixEnd_2737429 1405616834556675530148299 := by
  unfold tailWord_2737429
  simp only [CollatzResearch.WordTrace]
  refine ⟨99842237999769723497487341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66561491999846482331658227 99842237999769723497487341)
  ·
    refine ⟨37440839249913646311557753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99842237999769723497487341 37440839249913646311557753)
    ·
      refine ⟨28080629437435234733668315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37440839249913646311557753 28080629437435234733668315)
      ·
        refine ⟨42120944156152852100502473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28080629437435234733668315 42120944156152852100502473)
        ·
          refine ⟨31590708117114639075376855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42120944156152852100502473 31590708117114639075376855)
          ·
            refine ⟨47386062175671958613065283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31590708117114639075376855 47386062175671958613065283)
            ·
              refine ⟨71079093263507937919597925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47386062175671958613065283 71079093263507937919597925)
              ·
                refine ⟨13327329986907738359924611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71079093263507937919597925 13327329986907738359924611)
                ·
                  refine ⟨19990994980361607539886917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13327329986907738359924611 19990994980361607539886917)
                  ·
                    refine ⟨3748311558817801413728797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19990994980361607539886917 3748311558817801413728797)
                    ·
                      refine ⟨1405616834556675530148299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3748311558817801413728797 1405616834556675530148299)
                      ·
                        rfl

theorem cell23_2737429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_2737429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737429 prefixEnd_2737429 := by exact prefixLift 2737429
  have htrace : WordTrace (prefixWord ++ tailWord_2737429) baseStart_2737429 baseEnd_2737429 := by
    simpa [prefixWord, tailWord_2737429, baseEnd_2737429] using wordTrace_append hprefix tailTrace_2737429
  have hstable : (prefixWord ++ tailWord_2737429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737429).length < 2 ^ (prefixWord ++ tailWord_2737429).sum := by decide
  have hdescent : baseEnd_2737429 < baseStart_2737429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737486 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_2737486 : Nat := 118140960795 + 2737486 * 2 ^ 59
def prefixEnd_2737486 : Nat := 4983230072969 + 3 ^ 40 * 2737486 * 2
def baseEnd_2737486 : Nat := 1405646102953981807135537

theorem tailTrace_2737486 : CollatzResearch.WordTrace tailWord_2737486 prefixEnd_2737486 1405646102953981807135537 := by
  unfold tailWord_2737486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12480539620070402779039039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66562877973708814821541541 12480539620070402779039039)
  ·
    refine ⟨18720809430105604168558559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12480539620070402779039039 18720809430105604168558559)
    ·
      refine ⟨28081214145158406252837839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18720809430105604168558559 28081214145158406252837839)
      ·
        refine ⟨42121821217737609379256759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28081214145158406252837839 42121821217737609379256759)
        ·
          refine ⟨63182731826606414068885139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42121821217737609379256759 63182731826606414068885139)
          ·
            refine ⟨94774097739909621103327709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63182731826606414068885139 94774097739909621103327709)
            ·
              refine ⟨35540286652466107913747891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94774097739909621103327709 35540286652466107913747891)
              ·
                refine ⟨53310429978699161870621837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35540286652466107913747891 53310429978699161870621837)
                ·
                  refine ⟨19991411242012185701483189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53310429978699161870621837 19991411242012185701483189)
                  ·
                    refine ⟨1874194803938642409514049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19991411242012185701483189 1874194803938642409514049)
                    ·
                      refine ⟨1405646102953981807135537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874194803938642409514049 1405646102953981807135537)
                      ·
                        rfl

theorem cell23_2737486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_2737486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737486 prefixEnd_2737486 := by exact prefixLift 2737486
  have htrace : WordTrace (prefixWord ++ tailWord_2737486) baseStart_2737486 baseEnd_2737486 := by
    simpa [prefixWord, tailWord_2737486, baseEnd_2737486] using wordTrace_append hprefix tailTrace_2737486
  have hstable : (prefixWord ++ tailWord_2737486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737486).length < 2 ^ (prefixWord ++ tailWord_2737486).sum := by decide
  have hdescent : baseEnd_2737486 < baseStart_2737486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737493 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_2737493 : Nat := 118140960795 + 2737493 * 2 ^ 59
def prefixEnd_2737493 : Nat := 4983230072969 + 3 ^ 40 * 2737493 * 2
def baseEnd_2737493 : Nat := 1405649697318563279748005

theorem tailTrace_2737493 : CollatzResearch.WordTrace tailWord_2737493 prefixEnd_2737493 1405649697318563279748005 := by
  unfold tailWord_2737493
  simp only [CollatzResearch.WordTrace]
  refine ⟨99844572271537862427817133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66563048181025241618544755 99844572271537862427817133)
  ·
    refine ⟨37441714601826698410431425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99844572271537862427817133 37441714601826698410431425)
    ·
      refine ⟨28081285951370023807823569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37441714601826698410431425 28081285951370023807823569)
      ·
        refine ⟨21060964463527517855867677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28081285951370023807823569 21060964463527517855867677)
        ·
          refine ⟨7897861673822819195950379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21060964463527517855867677 7897861673822819195950379)
          ·
            refine ⟨11846792510734228793925569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897861673822819195950379 11846792510734228793925569)
            ·
              refine ⟨8885094383050671595444177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11846792510734228793925569 8885094383050671595444177)
              ·
                refine ⟨6663820787288003696583133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8885094383050671595444177 6663820787288003696583133)
                ·
                  refine ⟨2498932795233001386218675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6663820787288003696583133 2498932795233001386218675)
                  ·
                    refine ⟨3748399192849502079328013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2498932795233001386218675 3748399192849502079328013)
                    ·
                      refine ⟨1405649697318563279748005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3748399192849502079328013 1405649697318563279748005)
                      ·
                        rfl

theorem cell23_2737493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_2737493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737493 prefixEnd_2737493 := by exact prefixLift 2737493
  have htrace : WordTrace (prefixWord ++ tailWord_2737493) baseStart_2737493 baseEnd_2737493 := by
    simpa [prefixWord, tailWord_2737493, baseEnd_2737493] using wordTrace_append hprefix tailTrace_2737493
  have hstable : (prefixWord ++ tailWord_2737493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737493).length < 2 ^ (prefixWord ++ tailWord_2737493).sum := by decide
  have hdescent : baseEnd_2737493 < baseStart_2737493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737496 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 1, 5]
def baseStart_2737496 : Nat := 118140960795 + 2737496 * 2 ^ 59
def prefixEnd_2737496 : Nat := 4983230072969 + 3 ^ 40 * 2737496 * 2
def baseEnd_2737496 : Nat := 468550412586842256003497

theorem tailTrace_2737496 : CollatzResearch.WordTrace tailWord_2737496 prefixEnd_2737496 468550412586842256003497 := by
  unfold tailWord_2737496
  simp only [CollatzResearch.WordTrace]
  refine ⟨49922340845263496970088171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66563121127017995960117561 49922340845263496970088171)
  ·
    refine ⟨74883511267895245455132257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49922340845263496970088171 74883511267895245455132257)
    ·
      refine ⟨56162633450921434091349193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74883511267895245455132257 56162633450921434091349193)
      ·
        refine ⟨42121975088191075568511895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56162633450921434091349193 42121975088191075568511895)
        ·
          refine ⟨63182962632286613352767843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42121975088191075568511895 63182962632286613352767843)
          ·
            refine ⟨94774443948429920029151765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63182962632286613352767843 94774443948429920029151765)
            ·
              refine ⟨4442552060082652501366489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94774443948429920029151765 4442552060082652501366489)
              ·
                refine ⟨3331914045061989376024867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4442552060082652501366489 3331914045061989376024867)
                ·
                  refine ⟨4997871067592984064037301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331914045061989376024867 4997871067592984064037301)
                  ·
                    refine ⟨468550412586842256003497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4997871067592984064037301 468550412586842256003497)
                    ·
                      rfl

theorem cell23_2737496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_2737496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737496 prefixEnd_2737496 := by exact prefixLift 2737496
  have htrace : WordTrace (prefixWord ++ tailWord_2737496) baseStart_2737496 baseEnd_2737496 := by
    simpa [prefixWord, tailWord_2737496, baseEnd_2737496] using wordTrace_append hprefix tailTrace_2737496
  have hstable : (prefixWord ++ tailWord_2737496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737496).length < 2 ^ (prefixWord ++ tailWord_2737496).sum := by decide
  have hdescent : baseEnd_2737496 < baseStart_2737496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737509 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_2737509 : Nat := 118140960795 + 2737509 * 2 ^ 59
def prefixEnd_2737509 : Nat := 4983230072969 + 3 ^ 40 * 2737509 * 2
def baseEnd_2737509 : Nat := 468552637669678405715977

theorem tailTrace_2737509 : CollatzResearch.WordTrace tailWord_2737509 prefixEnd_2737509 468552637669678405715977 := by
  unfold tailWord_2737509
  simp only [CollatzResearch.WordTrace]
  refine ⟨99845155839479897160399581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66563437226319931440266387 99845155839479897160399581)
  ·
    refine ⟨37441933439804961435149843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99845155839479897160399581 37441933439804961435149843)
    ·
      refine ⟨56162900159707442152724765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37441933439804961435149843 56162900159707442152724765)
      ·
        refine ⟨21061087559890290807271787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56162900159707442152724765 21061087559890290807271787)
        ·
          refine ⟨31591631339835436210907681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21061087559890290807271787 31591631339835436210907681)
          ·
            refine ⟨23693723504876577158180761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31591631339835436210907681 23693723504876577158180761)
            ·
              refine ⟨17770292628657432868635571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23693723504876577158180761 17770292628657432868635571)
              ·
                refine ⟨26655438942986149302953357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17770292628657432868635571 26655438942986149302953357)
                ·
                  refine ⟨9995789603619805988607509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26655438942986149302953357 9995789603619805988607509)
                  ·
                    refine ⟨468552637669678405715977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9995789603619805988607509 468552637669678405715977)
                    ·
                      rfl

theorem cell23_2737509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_2737509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737509 prefixEnd_2737509 := by exact prefixLift 2737509
  have htrace : WordTrace (prefixWord ++ tailWord_2737509) baseStart_2737509 baseEnd_2737509 := by
    simpa [prefixWord, tailWord_2737509, baseEnd_2737509] using wordTrace_append hprefix tailTrace_2737509
  have hstable : (prefixWord ++ tailWord_2737509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737509).length < 2 ^ (prefixWord ++ tailWord_2737509).sum := by decide
  have hdescent : baseEnd_2737509 < baseStart_2737509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737529 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2737529 : Nat := 118140960795 + 2737529 * 2 ^ 59
def prefixEnd_2737529 : Nat := 4983230072969 + 3 ^ 40 * 2737529 * 2
def baseEnd_2737529 : Nat := 1405668182622125138897839

theorem tailTrace_2737529 : CollatzResearch.WordTrace tailWord_2737529 prefixEnd_2737529 1405668182622125138897839 := by
  unfold tailWord_2737529
  simp only [CollatzResearch.WordTrace]
  refine ⟨99845885299407440576127641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66563923532938293717418427 99845885299407440576127641)
  ·
    refine ⟨74884413974555580432095731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99845885299407440576127641 74884413974555580432095731)
    ·
      refine ⟨112326620961833370648143597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74884413974555580432095731 112326620961833370648143597)
      ·
        refine ⟨42122482860687513993053849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112326620961833370648143597 42122482860687513993053849)
        ·
          refine ⟨31591862145515635494790387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42122482860687513993053849 31591862145515635494790387)
          ·
            refine ⟨47387793218273453242185581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31591862145515635494790387 47387793218273453242185581)
            ·
              refine ⟨17770422456852544965819593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47387793218273453242185581 17770422456852544965819593)
              ·
                refine ⟨13327816842639408724364695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17770422456852544965819593 13327816842639408724364695)
                ·
                  refine ⟨19991725263959113086547043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13327816842639408724364695 19991725263959113086547043)
                  ·
                    refine ⟨29987587895938669629820565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19991725263959113086547043 29987587895938669629820565)
                    ·
                      refine ⟨1405668182622125138897839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29987587895938669629820565 1405668182622125138897839)
                      ·
                        rfl

theorem cell23_2737529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2737529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737529 prefixEnd_2737529 := by exact prefixLift 2737529
  have htrace : WordTrace (prefixWord ++ tailWord_2737529) baseStart_2737529 baseEnd_2737529 := by
    simpa [prefixWord, tailWord_2737529, baseEnd_2737529] using wordTrace_append hprefix tailTrace_2737529
  have hstable : (prefixWord ++ tailWord_2737529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737529).length < 2 ^ (prefixWord ++ tailWord_2737529).sum := by decide
  have hdescent : baseEnd_2737529 < baseStart_2737529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737534 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_2737534 : Nat := 118140960795 + 2737534 * 2 ^ 59
def prefixEnd_2737534 : Nat := 4983230072969 + 3 ^ 40 * 2737534 * 2
def baseEnd_2737534 : Nat := 156185638891710846592813

theorem tailTrace_2737534 : CollatzResearch.WordTrace tailWord_2737534 prefixEnd_2737534 156185638891710846592813 := by
  unfold tailWord_2737534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12480758458048665803757457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66564045109592884286706437 12480758458048665803757457)
  ·
    refine ⟨9360568843536499352818093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12480758458048665803757457 9360568843536499352818093)
    ·
      refine ⟨3510213316326187257306785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9360568843536499352818093 3510213316326187257306785)
      ·
        refine ⟨2632659987244640442980089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3510213316326187257306785 2632659987244640442980089)
        ·
          refine ⟨1974494990433480332235067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2632659987244640442980089 1974494990433480332235067)
          ·
            refine ⟨2961742485650220498352601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974494990433480332235067 2961742485650220498352601)
            ·
              refine ⟨2221306864237665373764451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2961742485650220498352601 2221306864237665373764451)
              ·
                refine ⟨3331960296356498060646677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221306864237665373764451 3331960296356498060646677)
                ·
                  refine ⟨156185638891710846592813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3331960296356498060646677 156185638891710846592813)
                  ·
                    rfl

theorem cell23_2737534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_2737534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737534 prefixEnd_2737534 := by exact prefixLift 2737534
  have htrace : WordTrace (prefixWord ++ tailWord_2737534) baseStart_2737534 baseEnd_2737534 := by
    simpa [prefixWord, tailWord_2737534, baseEnd_2737534] using wordTrace_append hprefix tailTrace_2737534
  have hstable : (prefixWord ++ tailWord_2737534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737534).length < 2 ^ (prefixWord ++ tailWord_2737534).sum := by decide
  have hdescent : baseEnd_2737534 < baseStart_2737534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737539 : List Nat := [1, 1, 1, 3, 5, 1, 1, 10]
def baseStart_2737539 : Nat := 118140960795 + 2737539 * 2 ^ 59
def prefixEnd_2737539 : Nat := 4983230072969 + 3 ^ 40 * 2737539 * 2
def baseEnd_2737539 : Nat := 52061974719580374065659

theorem tailTrace_2737539 : CollatzResearch.WordTrace tailWord_2737539 prefixEnd_2737539 52061974719580374065659 := by
  unfold tailWord_2737539
  simp only [CollatzResearch.WordTrace]
  refine ⟨99846250029371212283991671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66564166686247474855994447 99846250029371212283991671)
  ·
    refine ⟨149769375044056818425987507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99846250029371212283991671 149769375044056818425987507)
    ·
      refine ⟨224654062566085227638981261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149769375044056818425987507 224654062566085227638981261)
      ·
        refine ⟨84245273462281960364617973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224654062566085227638981261 84245273462281960364617973)
        ·
          refine ⟨7897994387088933784182935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84245273462281960364617973 7897994387088933784182935)
          ·
            refine ⟨11846991580633400676274403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897994387088933784182935 11846991580633400676274403)
            ·
              refine ⟨17770487370950101014411605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11846991580633400676274403 17770487370950101014411605)
              ·
                refine ⟨52061974719580374065659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17770487370950101014411605 52061974719580374065659)
                ·
                  rfl

theorem cell23_2737539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 10].length) (baseStart_2737539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737539 prefixEnd_2737539 := by exact prefixLift 2737539
  have htrace : WordTrace (prefixWord ++ tailWord_2737539) baseStart_2737539 baseEnd_2737539 := by
    simpa [prefixWord, tailWord_2737539, baseEnd_2737539] using wordTrace_append hprefix tailTrace_2737539
  have hstable : (prefixWord ++ tailWord_2737539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737539).length < 2 ^ (prefixWord ++ tailWord_2737539).sum := by decide
  have hdescent : baseEnd_2737539 < baseStart_2737539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737543 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 2, 4]
def baseStart_2737543 : Nat := 118140960795 + 2737543 * 2 ^ 59
def prefixEnd_2737543 : Nat := 4983230072969 + 3 ^ 40 * 2737543 * 2
def baseEnd_2737543 : Nat := 468558457117096028040925

theorem tailTrace_2737543 : CollatzResearch.WordTrace tailWord_2737543 prefixEnd_2737543 468558457117096028040925 := by
  unfold tailWord_2737543
  simp only [CollatzResearch.WordTrace]
  refine ⟨99846395921356720967137283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66564263947571147311424855 99846395921356720967137283)
  ·
    refine ⟨149769593882035081450705925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99846395921356720967137283 149769593882035081450705925)
    ·
      refine ⟨28081798852881577772007361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149769593882035081450705925 28081798852881577772007361)
      ·
        refine ⟨21061349139661183329005521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28081798852881577772007361 21061349139661183329005521)
        ·
          refine ⟨15796011854745887496754141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21061349139661183329005521 15796011854745887496754141)
          ·
            refine ⟨5923504445529707811282803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15796011854745887496754141 5923504445529707811282803)
            ·
              refine ⟨8885256668294561716924205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5923504445529707811282803 8885256668294561716924205)
              ·
                refine ⟨3331971250610460643846577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8885256668294561716924205 3331971250610460643846577)
                ·
                  refine ⟨2498978437957845482884933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3331971250610460643846577 2498978437957845482884933)
                  ·
                    refine ⟨468558457117096028040925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2498978437957845482884933 468558457117096028040925)
                    ·
                      rfl

theorem cell23_2737543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_2737543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737543 prefixEnd_2737543 := by exact prefixLift 2737543
  have htrace : WordTrace (prefixWord ++ tailWord_2737543) baseStart_2737543 baseEnd_2737543 := by
    simpa [prefixWord, tailWord_2737543, baseEnd_2737543] using wordTrace_append hprefix tailTrace_2737543
  have hstable : (prefixWord ++ tailWord_2737543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737543).length < 2 ^ (prefixWord ++ tailWord_2737543).sum := by decide
  have hdescent : baseEnd_2737543 < baseStart_2737543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737556 : List Nat := [2, 4, 2, 1, 2, 1, 2, 9]
def baseStart_2737556 : Nat := 118140960795 + 2737556 * 2 ^ 59
def prefixEnd_2737556 : Nat := 4983230072969 + 3 ^ 40 * 2737556 * 2
def baseEnd_2737556 : Nat := 52062298022214686417045

theorem tailTrace_2737556 : CollatzResearch.WordTrace tailWord_2737556 prefixEnd_2737556 52062298022214686417045 := by
  unfold tailWord_2737556
  simp only [CollatzResearch.WordTrace]
  refine ⟨49923435035154812093680261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66564580046873082791573681 49923435035154812093680261)
  ·
    refine ⟨9360644069091527267565049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49923435035154812093680261 9360644069091527267565049)
    ·
      refine ⟨7020483051818645450673787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9360644069091527267565049 7020483051818645450673787)
      ·
        refine ⟨10530724577727968176010681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7020483051818645450673787 10530724577727968176010681)
        ·
          refine ⟨7898043433295976132008011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10530724577727968176010681 7898043433295976132008011)
          ·
            refine ⟨11847065149943964198012017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7898043433295976132008011 11847065149943964198012017)
            ·
              refine ⟨8885298862457973148509013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11847065149943964198012017 8885298862457973148509013)
              ·
                refine ⟨52062298022214686417045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8885298862457973148509013 52062298022214686417045)
                ·
                  rfl

theorem cell23_2737556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 9].length) (baseStart_2737556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737556 prefixEnd_2737556 := by exact prefixLift 2737556
  have htrace : WordTrace (prefixWord ++ tailWord_2737556) baseStart_2737556 baseEnd_2737556 := by
    simpa [prefixWord, tailWord_2737556, baseEnd_2737556] using wordTrace_append hprefix tailTrace_2737556
  have hstable : (prefixWord ++ tailWord_2737556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737556).length < 2 ^ (prefixWord ++ tailWord_2737556).sum := by decide
  have hdescent : baseEnd_2737556 < baseStart_2737556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737640 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_2737640 : Nat := 118140960795 + 2737640 * 2 ^ 59
def prefixEnd_2737640 : Nat := 4983230072969 + 3 ^ 40 * 2737640 * 2
def baseEnd_2737640 : Nat := 1405725178974774204609829

theorem tailTrace_2737640 : CollatzResearch.WordTrace tailWord_2737640 prefixEnd_2737640 1405725178974774204609829 := by
  unfold tailWord_2737640
  simp only [CollatzResearch.WordTrace]
  refine ⟨49924966901002653266709187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66566622534670204355612249 49924966901002653266709187)
  ·
    refine ⟨74887450351503979900063781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49924966901002653266709187 74887450351503979900063781)
    ·
      refine ⟨14041396940906996231261959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74887450351503979900063781 14041396940906996231261959)
      ·
        refine ⟨21062095411360494346892939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14041396940906996231261959 21062095411360494346892939)
        ·
          refine ⟨31593143117040741520339409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21062095411360494346892939 31593143117040741520339409)
          ·
            refine ⟨23694857337780556140254557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31593143117040741520339409 23694857337780556140254557)
            ·
              refine ⟨8885571501667708552595459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23694857337780556140254557 8885571501667708552595459)
              ·
                refine ⟨13328357252501562828893189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8885571501667708552595459 13328357252501562828893189)
                ·
                  refine ⟨2499066984844043030417473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13328357252501562828893189 2499066984844043030417473)
                  ·
                    refine ⟨1874300238633032272813105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2499066984844043030417473 1874300238633032272813105)
                    ·
                      refine ⟨1405725178974774204609829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874300238633032272813105 1405725178974774204609829)
                      ·
                        rfl

theorem cell23_2737640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_2737640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737640 prefixEnd_2737640 := by exact prefixLift 2737640
  have htrace : WordTrace (prefixWord ++ tailWord_2737640) baseStart_2737640 baseEnd_2737640 := by
    simpa [prefixWord, tailWord_2737640, baseEnd_2737640] using wordTrace_append hprefix tailTrace_2737640
  have hstable : (prefixWord ++ tailWord_2737640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737640).length < 2 ^ (prefixWord ++ tailWord_2737640).sum := by decide
  have hdescent : baseEnd_2737640 < baseStart_2737640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737677 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2737677 : Nat := 118140960795 + 2737677 * 2 ^ 59
def prefixEnd_2737677 : Nat := 4983230072969 + 3 ^ 40 * 2737677 * 2
def baseEnd_2737677 : Nat := 1405744177758990559847159

theorem tailTrace_2737677 : CollatzResearch.WordTrace tailWord_2737677 prefixEnd_2737677 1405744177758990559847159 := by
  unfold tailWord_2737677
  simp only [CollatzResearch.WordTrace]
  refine ⟨99851283302871261852515285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66567522201914174568343523 99851283302871261852515285)
  ·
    refine ⟨2340264452411045199668327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 99851283302871261852515285 2340264452411045199668327)
    ·
      refine ⟨3510396678616567799502491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340264452411045199668327 3510396678616567799502491)
      ·
        refine ⟨5265595017924851699253737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3510396678616567799502491 5265595017924851699253737)
        ·
          refine ⟨3949196263443638774440303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5265595017924851699253737 3949196263443638774440303)
          ·
            refine ⟨5923794395165458161660455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949196263443638774440303 5923794395165458161660455)
            ·
              refine ⟨8885691592748187242490683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5923794395165458161660455 8885691592748187242490683)
              ·
                refine ⟨13328537389122280863736025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8885691592748187242490683 13328537389122280863736025)
                ·
                  refine ⟨9996403041841710647802019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13328537389122280863736025 9996403041841710647802019)
                  ·
                    refine ⟨14994604562762565971703029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9996403041841710647802019 14994604562762565971703029)
                    ·
                      refine ⟨1405744177758990559847159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14994604562762565971703029 1405744177758990559847159)
                      ·
                        rfl

theorem cell23_2737677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2737677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737677 prefixEnd_2737677 := by exact prefixLift 2737677
  have htrace : WordTrace (prefixWord ++ tailWord_2737677) baseStart_2737677 baseEnd_2737677 := by
    simpa [prefixWord, tailWord_2737677, baseEnd_2737677] using wordTrace_append hprefix tailTrace_2737677
  have hstable : (prefixWord ++ tailWord_2737677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737677).length < 2 ^ (prefixWord ++ tailWord_2737677).sum := by decide
  have hdescent : baseEnd_2737677 < baseStart_2737677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737693 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2737693 : Nat := 118140960795 + 2737693 * 2 ^ 59
def prefixEnd_2737693 : Nat := 4983230072969 + 3 ^ 40 * 2737693 * 2
def baseEnd_2737693 : Nat := 468584131149820832415695

theorem tailTrace_2737693 : CollatzResearch.WordTrace tailWord_2737693 prefixEnd_2737693 468584131149820832415695 := by
  unfold tailWord_2737693
  simp only [CollatzResearch.WordTrace]
  refine ⟨99851866870813296585097733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66567911247208864390065155 99851866870813296585097733)
  ·
    refine ⟨18722225038277493109705825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99851866870813296585097733 18722225038277493109705825)
    ·
      refine ⟨14041668778708119832279369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18722225038277493109705825 14041668778708119832279369)
      ·
        refine ⟨10531251584031089874209527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14041668778708119832279369 10531251584031089874209527)
        ·
          refine ⟨15796877376046634811314291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10531251584031089874209527 15796877376046634811314291)
          ·
            refine ⟨23695316064069952216971437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15796877376046634811314291 23695316064069952216971437)
            ·
              refine ⟨8885743524026232081364289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23695316064069952216971437 8885743524026232081364289)
              ·
                refine ⟨6664307643019674061023217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8885743524026232081364289 6664307643019674061023217)
                ·
                  refine ⟨4998230732264755545767413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6664307643019674061023217 4998230732264755545767413)
                  ·
                    refine ⟨468584131149820832415695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4998230732264755545767413 468584131149820832415695)
                    ·
                      rfl

theorem cell23_2737693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2737693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737693 prefixEnd_2737693 := by exact prefixLift 2737693
  have htrace : WordTrace (prefixWord ++ tailWord_2737693) baseStart_2737693 baseEnd_2737693 := by
    simpa [prefixWord, tailWord_2737693, baseEnd_2737693] using wordTrace_append hprefix tailTrace_2737693
  have hstable : (prefixWord ++ tailWord_2737693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737693).length < 2 ^ (prefixWord ++ tailWord_2737693).sum := by decide
  have hdescent : baseEnd_2737693 < baseStart_2737693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737713 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 1, 6, 2]
def baseStart_2737713 : Nat := 118140960795 + 2737713 * 2 ^ 59
def prefixEnd_2737713 : Nat := 4983230072969 + 3 ^ 40 * 2737713 * 2
def baseEnd_2737713 : Nat := 1405762663062552418996993

theorem tailTrace_2737713 : CollatzResearch.WordTrace tailWord_2737713 prefixEnd_2737713 1405762663062552418996993 := by
  unfold tailWord_2737713
  simp only [CollatzResearch.WordTrace]
  refine ⟨99852596330740840000825793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66568397553827226667217195 99852596330740840000825793)
  ·
    refine ⟨74889447248055630000619345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99852596330740840000825793 74889447248055630000619345)
    ·
      refine ⟨56167085436041722500464509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74889447248055630000619345 56167085436041722500464509)
      ·
        refine ⟨21062657038515645937674191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56167085436041722500464509 21062657038515645937674191)
        ·
          refine ⟨31593985557773468906511287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21062657038515645937674191 31593985557773468906511287)
          ·
            refine ⟨47390978336660203359766931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31593985557773468906511287 47390978336660203359766931)
            ·
              refine ⟨71086467504990305039650397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47390978336660203359766931 71086467504990305039650397)
              ·
                refine ⟨26657425314371364389868899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71086467504990305039650397 26657425314371364389868899)
                ·
                  refine ⟨39986137971557046584803349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26657425314371364389868899 39986137971557046584803349)
                  ·
                    refine ⟨1874350217416736558662657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39986137971557046584803349 1874350217416736558662657)
                    ·
                      refine ⟨1405762663062552418996993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874350217416736558662657 1405762663062552418996993)
                      ·
                        rfl

theorem cell23_2737713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_2737713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737713 prefixEnd_2737713 := by exact prefixLift 2737713
  have htrace : WordTrace (prefixWord ++ tailWord_2737713) baseStart_2737713 baseEnd_2737713 := by
    simpa [prefixWord, tailWord_2737713, baseEnd_2737713] using wordTrace_append hprefix tailTrace_2737713
  have hstable : (prefixWord ++ tailWord_2737713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737713).length < 2 ^ (prefixWord ++ tailWord_2737713).sum := by decide
  have hdescent : baseEnd_2737713 < baseStart_2737713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737783 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 1, 5]
def baseStart_2737783 : Nat := 118140960795 + 2737783 * 2 ^ 59
def prefixEnd_2737783 : Nat := 4983230072969 + 3 ^ 40 * 2737783 * 2
def baseEnd_2737783 : Nat := 468599535569455715040557

theorem tailTrace_2737783 : CollatzResearch.WordTrace tailWord_2737783 prefixEnd_2737783 468599535569455715040557 := by
  unfold tailWord_2737783
  simp only [CollatzResearch.WordTrace]
  refine ⟨99855149440487241955874003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66570099626991494637249335 99855149440487241955874003)
  ·
    refine ⟨149782724160730862933811005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99855149440487241955874003 149782724160730862933811005)
    ·
      refine ⟨56168521560274073600179127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149782724160730862933811005 56168521560274073600179127)
      ·
        refine ⟨84252782340411110400268691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56168521560274073600179127 84252782340411110400268691)
        ·
          refine ⟨126379173510616665600403037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84252782340411110400268691 126379173510616665600403037)
          ·
            refine ⟨47392190066481249600151139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126379173510616665600403037 47392190066481249600151139)
            ·
              refine ⟨71088285099721874400226709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47392190066481249600151139 71088285099721874400226709)
              ·
                refine ⟨3332263364049462862510627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71088285099721874400226709 3332263364049462862510627)
                ·
                  refine ⟨4998395046074194293765941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332263364049462862510627 4998395046074194293765941)
                  ·
                    refine ⟨468599535569455715040557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4998395046074194293765941 468599535569455715040557)
                    ·
                      rfl

theorem cell23_2737783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_2737783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737783 prefixEnd_2737783 := by exact prefixLift 2737783
  have htrace : WordTrace (prefixWord ++ tailWord_2737783) baseStart_2737783 baseEnd_2737783 := by
    simpa [prefixWord, tailWord_2737783, baseEnd_2737783] using wordTrace_append hprefix tailTrace_2737783
  have hstable : (prefixWord ++ tailWord_2737783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737783).length < 2 ^ (prefixWord ++ tailWord_2737783).sum := by decide
  have hdescent : baseEnd_2737783 < baseStart_2737783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737837 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_2737837 : Nat := 118140960795 + 2737837 * 2 ^ 59
def prefixEnd_2737837 : Nat := 4983230072969 + 3 ^ 40 * 2737837 * 2
def baseEnd_2737837 : Nat := 1405826334663709933846423

theorem tailTrace_2737837 : CollatzResearch.WordTrace tailWord_2737837 prefixEnd_2737837 1405826334663709933846423 := by
  unfold tailWord_2737837
  simp only [CollatzResearch.WordTrace]
  refine ⟨99857118982291609178339765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66571412654861072785559843 99857118982291609178339765)
  ·
    refine ⟨9361604904589838360469353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99857118982291609178339765 9361604904589838360469353)
    ·
      refine ⟨7021203678442378770352015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9361604904589838360469353 7021203678442378770352015)
      ·
        refine ⟨10531805517663568155528023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7021203678442378770352015 10531805517663568155528023)
        ·
          refine ⟨15797708276495352233292035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10531805517663568155528023 15797708276495352233292035)
          ·
            refine ⟨23696562414743028349938053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15797708276495352233292035 23696562414743028349938053)
            ·
              refine ⟨4443105452764317815613385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23696562414743028349938053 4443105452764317815613385)
              ·
                refine ⟨3332329089573238361710039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4443105452764317815613385 3332329089573238361710039)
                ·
                  refine ⟨4998493634359857542565059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332329089573238361710039 4998493634359857542565059)
                  ·
                    refine ⟨7497740451539786313847589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4998493634359857542565059 7497740451539786313847589)
                    ·
                      refine ⟨1405826334663709933846423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7497740451539786313847589 1405826334663709933846423)
                      ·
                        rfl

theorem cell23_2737837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_2737837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737837 prefixEnd_2737837 := by exact prefixLift 2737837
  have htrace : WordTrace (prefixWord ++ tailWord_2737837) baseStart_2737837 baseEnd_2737837 := by
    simpa [prefixWord, tailWord_2737837, baseEnd_2737837] using wordTrace_append hprefix tailTrace_2737837
  have hstable : (prefixWord ++ tailWord_2737837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737837).length < 2 ^ (prefixWord ++ tailWord_2737837).sum := by decide
  have hdescent : baseEnd_2737837 < baseStart_2737837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737840 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 3]
def baseStart_2737840 : Nat := 118140960795 + 2737840 * 2 ^ 59
def prefixEnd_2737840 : Nat := 4983230072969 + 3 ^ 40 * 2737840 * 2
def baseEnd_2737840 : Nat := 1405827875105673422108909

theorem tailTrace_2737840 : CollatzResearch.WordTrace tailWord_2737840 prefixEnd_2737840 1405827875105673422108909 := by
  unfold tailWord_2737840
  simp only [CollatzResearch.WordTrace]
  refine ⟨49928614200640370345349487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66571485600853827127132649 49928614200640370345349487)
  ·
    refine ⟨74892921300960555518024231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49928614200640370345349487 74892921300960555518024231)
    ·
      refine ⟨112339381951440833277036347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74892921300960555518024231 112339381951440833277036347)
      ·
        refine ⟨168509072927161249915554521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112339381951440833277036347 168509072927161249915554521)
        ·
          refine ⟨126381804695370937436665891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168509072927161249915554521 126381804695370937436665891)
          ·
            refine ⟨189572707043056406154998837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126381804695370937436665891 189572707043056406154998837)
            ·
              refine ⟨17772441285286538077031141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189572707043056406154998837 17772441285286538077031141)
              ·
                refine ⟨3332332740991225889443339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17772441285286538077031141 3332332740991225889443339)
                ·
                  refine ⟨4998499111486838834165009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332332740991225889443339 4998499111486838834165009)
                  ·
                    refine ⟨3748874333615129125623757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4998499111486838834165009 3748874333615129125623757)
                    ·
                      refine ⟨1405827875105673422108909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3748874333615129125623757 1405827875105673422108909)
                      ·
                        rfl

theorem cell23_2737840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 3].length) (baseStart_2737840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737840 prefixEnd_2737840 := by exact prefixLift 2737840
  have htrace : WordTrace (prefixWord ++ tailWord_2737840) baseStart_2737840 baseEnd_2737840 := by
    simpa [prefixWord, tailWord_2737840, baseEnd_2737840] using wordTrace_append hprefix tailTrace_2737840
  have hstable : (prefixWord ++ tailWord_2737840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737840).length < 2 ^ (prefixWord ++ tailWord_2737840).sum := by decide
  have hdescent : baseEnd_2737840 < baseStart_2737840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737858 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_2737858 : Nat := 118140960795 + 2737858 * 2 ^ 59
def prefixEnd_2737858 : Nat := 4983230072969 + 3 ^ 40 * 2737858 * 2
def baseEnd_2737858 : Nat := 1405837117757454351683827

theorem tailTrace_2737858 : CollatzResearch.WordTrace tailWord_2737858 prefixEnd_2737858 1405837117757454351683827 := by
  unfold tailWord_2737858
  simp only [CollatzResearch.WordTrace]
  refine ⟨24964471228803882441213557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66571923276810353176569485 24964471228803882441213557)
  ·
    refine ⟨2340419177700363978863771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24964471228803882441213557 2340419177700363978863771)
    ·
      refine ⟨3510628766550545968295657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340419177700363978863771 3510628766550545968295657)
      ·
        refine ⟨2632971574912909476221743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3510628766550545968295657 2632971574912909476221743)
        ·
          refine ⟨3949457362369364214332615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2632971574912909476221743 3949457362369364214332615)
          ·
            refine ⟨5924186043554046321498923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949457362369364214332615 5924186043554046321498923)
            ·
              refine ⟨8886279065331069482248385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5924186043554046321498923 8886279065331069482248385)
              ·
                refine ⟨6664709298998302111686289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8886279065331069482248385 6664709298998302111686289)
                ·
                  refine ⟨4998531974248726583764717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6664709298998302111686289 4998531974248726583764717)
                  ·
                    refine ⟨1874449490343272468911769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4998531974248726583764717 1874449490343272468911769)
                    ·
                      refine ⟨1405837117757454351683827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874449490343272468911769 1405837117757454351683827)
                      ·
                        rfl

theorem cell23_2737858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_2737858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737858 prefixEnd_2737858 := by exact prefixLift 2737858
  have htrace : WordTrace (prefixWord ++ tailWord_2737858) baseStart_2737858 baseEnd_2737858 := by
    simpa [prefixWord, tailWord_2737858, baseEnd_2737858] using wordTrace_append hprefix tailTrace_2737858
  have hstable : (prefixWord ++ tailWord_2737858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737858).length < 2 ^ (prefixWord ++ tailWord_2737858).sum := by decide
  have hdescent : baseEnd_2737858 < baseStart_2737858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737887 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 3]
def baseStart_2737887 : Nat := 118140960795 + 2737887 * 2 ^ 59
def prefixEnd_2737887 : Nat := 4983230072969 + 3 ^ 40 * 2737887 * 2
def baseEnd_2737887 : Nat := 1405852008696434738221193

theorem tailTrace_2737887 : CollatzResearch.WordTrace tailWord_2737887 prefixEnd_2737887 1405852008696434738221193 := by
  unfold tailWord_2737887
  simp only [CollatzResearch.WordTrace]
  refine ⟨99858942632110467717659915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66572628421406978478439943 99858942632110467717659915)
  ·
    refine ⟨149788413948165701576489873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99858942632110467717659915 149788413948165701576489873)
    ·
      refine ⟨112341310461124276182367405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149788413948165701576489873 112341310461124276182367405)
      ·
        refine ⟨42127991422921603568387777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112341310461124276182367405 42127991422921603568387777)
        ·
          refine ⟨31595993567191202676290833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42127991422921603568387777 31595993567191202676290833)
          ·
            refine ⟨23696995175393402007218125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31595993567191202676290833 23696995175393402007218125)
            ·
              refine ⟨8886373190772525752706797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23696995175393402007218125 8886373190772525752706797)
              ·
                refine ⟨3332389946539697157265049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8886373190772525752706797 3332389946539697157265049)
                ·
                  refine ⟨2499292459904772867948787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3332389946539697157265049 2499292459904772867948787)
                  ·
                    refine ⟨3748938689857159301923181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2499292459904772867948787 3748938689857159301923181)
                    ·
                      refine ⟨1405852008696434738221193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3748938689857159301923181 1405852008696434738221193)
                      ·
                        rfl

theorem cell23_2737887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_2737887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737887 prefixEnd_2737887 := by exact prefixLift 2737887
  have htrace : WordTrace (prefixWord ++ tailWord_2737887) baseStart_2737887 baseEnd_2737887 := by
    simpa [prefixWord, tailWord_2737887, baseEnd_2737887] using wordTrace_append hprefix tailTrace_2737887
  have hstable : (prefixWord ++ tailWord_2737887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737887).length < 2 ^ (prefixWord ++ tailWord_2737887).sum := by decide
  have hdescent : baseEnd_2737887 < baseStart_2737887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737891 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 1, 2, 3]
def baseStart_2737891 : Nat := 118140960795 + 2737891 * 2 ^ 59
def prefixEnd_2737891 : Nat := 4983230072969 + 3 ^ 40 * 2737891 * 2
def baseEnd_2737891 : Nat := 1405854062619052722571175

theorem tailTrace_2737891 : CollatzResearch.WordTrace tailWord_2737891 prefixEnd_2737891 1405854062619052722571175 := by
  unfold tailWord_2737891
  simp only [CollatzResearch.WordTrace]
  refine ⟨99859088524095976400805527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66572725682730650933870351 99859088524095976400805527)
  ·
    refine ⟨149788632786143964601208291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99859088524095976400805527 149788632786143964601208291)
    ·
      refine ⟨224682949179215946901812437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149788632786143964601208291 224682949179215946901812437)
      ·
        refine ⟨5266006621387873755511229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 224682949179215946901812437 5266006621387873755511229)
        ·
          refine ⟨1974752483020452658316711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5266006621387873755511229 1974752483020452658316711)
          ·
            refine ⟨2962128724530678987475067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974752483020452658316711 2962128724530678987475067)
            ·
              refine ⟨4443193086796018481212601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962128724530678987475067 4443193086796018481212601)
              ·
                refine ⟨3332394815097013860909451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4443193086796018481212601 3332394815097013860909451)
                ·
                  refine ⟨4998592222645520791364177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332394815097013860909451 4998592222645520791364177)
                  ·
                    refine ⟨3748944166984140593523133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4998592222645520791364177 3748944166984140593523133)
                    ·
                      refine ⟨1405854062619052722571175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3748944166984140593523133 1405854062619052722571175)
                      ·
                        rfl

theorem cell23_2737891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_2737891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737891 prefixEnd_2737891 := by exact prefixLift 2737891
  have htrace : WordTrace (prefixWord ++ tailWord_2737891) baseStart_2737891 baseEnd_2737891 := by
    simpa [prefixWord, tailWord_2737891, baseEnd_2737891] using wordTrace_append hprefix tailTrace_2737891
  have hstable : (prefixWord ++ tailWord_2737891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737891).length < 2 ^ (prefixWord ++ tailWord_2737891).sum := by decide
  have hdescent : baseEnd_2737891 < baseStart_2737891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737908 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2737908 : Nat := 118140960795 + 2737908 * 2 ^ 59
def prefixEnd_2737908 : Nat := 4983230072969 + 3 ^ 40 * 2737908 * 2
def baseEnd_2737908 : Nat := 1405862791790179156058597

theorem tailTrace_2737908 : CollatzResearch.WordTrace tailWord_2737908 prefixEnd_2737908 1405862791790179156058597 := by
  unfold tailWord_2737908
  simp only [CollatzResearch.WordTrace]
  refine ⟨49929854282517194152087189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66573139043356258869449585 49929854282517194152087189)
  ·
    refine ⟨2340461919492993475879087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49929854282517194152087189 2340461919492993475879087)
    ·
      refine ⟨3510692879239490213818631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340461919492993475879087 3510692879239490213818631)
      ·
        refine ⟨5266039318859235320727947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3510692879239490213818631 5266039318859235320727947)
        ·
          refine ⟨7899058978288852981091921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5266039318859235320727947 7899058978288852981091921)
          ·
            refine ⟨5924294233716639735818941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7899058978288852981091921 5924294233716639735818941)
            ·
              refine ⟨2221610337643739900932103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5924294233716639735818941 2221610337643739900932103)
              ·
                refine ⟨3332415506465609851398155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221610337643739900932103 3332415506465609851398155)
                ·
                  refine ⟨4998623259698414777097233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332415506465609851398155 4998623259698414777097233)
                  ·
                    refine ⟨3748967444773811082822925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4998623259698414777097233 3748967444773811082822925)
                    ·
                      refine ⟨1405862791790179156058597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3748967444773811082822925 1405862791790179156058597)
                      ·
                        rfl

theorem cell23_2737908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2737908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737908 prefixEnd_2737908 := by exact prefixLift 2737908
  have htrace : WordTrace (prefixWord ++ tailWord_2737908) baseStart_2737908 baseEnd_2737908 := by
    simpa [prefixWord, tailWord_2737908, baseEnd_2737908] using wordTrace_append hprefix tailTrace_2737908
  have hstable : (prefixWord ++ tailWord_2737908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737908).length < 2 ^ (prefixWord ++ tailWord_2737908).sum := by decide
  have hdescent : baseEnd_2737908 < baseStart_2737908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737930 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_2737930 : Nat := 118140960795 + 2737930 * 2 ^ 59
def prefixEnd_2737930 : Nat := 4983230072969 + 3 ^ 40 * 2737930 * 2
def baseEnd_2737930 : Nat := 1405874088364578069983495

theorem tailTrace_2737930 : CollatzResearch.WordTrace tailWord_2737930 prefixEnd_2737930 1405874088364578069983495 := by
  unfold tailWord_2737930
  simp only [CollatzResearch.WordTrace]
  refine ⟨24965127742738671515368811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66573673980636457374316829 24965127742738671515368811)
  ·
    refine ⟨37447691614108007273053217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24965127742738671515368811 37447691614108007273053217)
    ·
      refine ⟨28085768710581005454789913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37447691614108007273053217 28085768710581005454789913)
      ·
        refine ⟨21064326532935754091092435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28085768710581005454789913 21064326532935754091092435)
        ·
          refine ⟨31596489799403631136638653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21064326532935754091092435 31596489799403631136638653)
          ·
            refine ⟨11848683674776361676239495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31596489799403631136638653 11848683674776361676239495)
            ·
              refine ⟨17773025512164542514359243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11848683674776361676239495 17773025512164542514359243)
              ·
                refine ⟨26659538268246813771538865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17773025512164542514359243 26659538268246813771538865)
                ·
                  refine ⟨19994653701185110328654149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26659538268246813771538865 19994653701185110328654149)
                  ·
                    refine ⟨3748997568972208186622653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19994653701185110328654149 3748997568972208186622653)
                    ·
                      refine ⟨1405874088364578069983495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3748997568972208186622653 1405874088364578069983495)
                      ·
                        rfl

theorem cell23_2737930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_2737930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737930 prefixEnd_2737930 := by exact prefixLift 2737930
  have htrace : WordTrace (prefixWord ++ tailWord_2737930) baseStart_2737930 baseEnd_2737930 := by
    simpa [prefixWord, tailWord_2737930, baseEnd_2737930] using wordTrace_append hprefix tailTrace_2737930
  have hstable : (prefixWord ++ tailWord_2737930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737930).length < 2 ^ (prefixWord ++ tailWord_2737930).sum := by decide
  have hdescent : baseEnd_2737930 < baseStart_2737930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737944 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 2, 2, 2]
def baseStart_2737944 : Nat := 118140960795 + 2737944 * 2 ^ 59
def prefixEnd_2737944 : Nat := 4983230072969 + 3 ^ 40 * 2737944 * 2
def baseEnd_2737944 : Nat := 1405881277093741015208431

theorem tailTrace_2737944 : CollatzResearch.WordTrace tailWord_2737944 prefixEnd_2737944 1405881277093741015208431 := by
  unfold tailWord_2737944
  simp only [CollatzResearch.WordTrace]
  refine ⟨49930510796451983226242443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66574014395269310968323257 49930510796451983226242443)
  ·
    refine ⟨74895766194677974839363665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49930510796451983226242443 74895766194677974839363665)
    ·
      refine ⟨56171824646008481129522749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74895766194677974839363665 56171824646008481129522749)
      ·
        refine ⟨21064434242253180423571031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56171824646008481129522749 21064434242253180423571031)
        ·
          refine ⟨31596651363379770635356547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21064434242253180423571031 31596651363379770635356547)
          ·
            refine ⟨47394977045069655953034821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31596651363379770635356547 47394977045069655953034821)
            ·
              refine ⟨8886558195950560491194029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47394977045069655953034821 8886558195950560491194029)
              ·
                refine ⟨3332459323481460184197761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8886558195950560491194029 3332459323481460184197761)
                ·
                  refine ⟨2499344492611095138148321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3332459323481460184197761 2499344492611095138148321)
                  ·
                    refine ⟨1874508369458321353611241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2499344492611095138148321 1874508369458321353611241)
                    ·
                      refine ⟨1405881277093741015208431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874508369458321353611241 1405881277093741015208431)
                      ·
                        rfl

theorem cell23_2737944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_2737944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737944 prefixEnd_2737944 := by exact prefixLift 2737944
  have htrace : WordTrace (prefixWord ++ tailWord_2737944) baseStart_2737944 baseEnd_2737944 := by
    simpa [prefixWord, tailWord_2737944, baseEnd_2737944] using wordTrace_append hprefix tailTrace_2737944
  have hstable : (prefixWord ++ tailWord_2737944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737944).length < 2 ^ (prefixWord ++ tailWord_2737944).sum := by decide
  have hdescent : baseEnd_2737944 < baseStart_2737944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737980 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_2737980 : Nat := 118140960795 + 2737980 * 2 ^ 59
def prefixEnd_2737980 : Nat := 4983230072969 + 3 ^ 40 * 2737980 * 2
def baseEnd_2737980 : Nat := 468633254132434291452755

theorem tailTrace_2737980 : CollatzResearch.WordTrace tailWord_2737980 prefixEnd_2737980 468633254132434291452755 := by
  unfold tailWord_2737980
  simp only [CollatzResearch.WordTrace]
  refine ⟨49931167310386772300397697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66574889747182363067196929 49931167310386772300397697)
  ·
    refine ⟨37448375482790079225298273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49931167310386772300397697 37448375482790079225298273)
    ·
      refine ⟨28086281612092559418973705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37448375482790079225298273 28086281612092559418973705)
      ·
        refine ⟨21064711209069419564230279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28086281612092559418973705 21064711209069419564230279)
        ·
          refine ⟨31597066813604129346345419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21064711209069419564230279 31597066813604129346345419)
          ·
            refine ⟨47395600220406194019518129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31597066813604129346345419 47395600220406194019518129)
            ·
              refine ⟨35546700165304645514638597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47395600220406194019518129 35546700165304645514638597)
              ·
                refine ⟨6665006280994621033994737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35546700165304645514638597 6665006280994621033994737)
                ·
                  refine ⟨4998754710745965775496053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6665006280994621033994737 4998754710745965775496053)
                  ·
                    refine ⟨468633254132434291452755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4998754710745965775496053 468633254132434291452755)
                    ·
                      rfl

theorem cell23_2737980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_2737980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737980 prefixEnd_2737980 := by exact prefixLift 2737980
  have htrace : WordTrace (prefixWord ++ tailWord_2737980) baseStart_2737980 baseEnd_2737980 := by
    simpa [prefixWord, tailWord_2737980, baseEnd_2737980] using wordTrace_append hprefix tailTrace_2737980
  have hstable : (prefixWord ++ tailWord_2737980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737980).length < 2 ^ (prefixWord ++ tailWord_2737980).sum := by decide
  have hdescent : baseEnd_2737980 < baseStart_2737980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2737997 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_2737997 : Nat := 118140960795 + 2737997 * 2 ^ 59
def prefixEnd_2737997 : Nat := 4983230072969 + 3 ^ 40 * 2737997 * 2
def baseEnd_2737997 : Nat := 468636163856143102615229

theorem tailTrace_2737997 : CollatzResearch.WordTrace tailWord_2737997 prefixEnd_2737997 468636163856143102615229 := by
  unfold tailWord_2737997
  simp only [CollatzResearch.WordTrace]
  refine ⟨99862954661711956504164245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66575303107807971002776163 99862954661711956504164245)
  ·
    refine ⟨4681075999767747961132699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99862954661711956504164245 4681075999767747961132699)
    ·
      refine ⟨7021613999651621941699049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4681075999767747961132699 7021613999651621941699049)
      ·
        refine ⟨5266210499738716456274287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7021613999651621941699049 5266210499738716456274287)
        ·
          refine ⟨7899315749608074684411431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5266210499738716456274287 7899315749608074684411431)
          ·
            refine ⟨11848973624412112026617147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7899315749608074684411431 11848973624412112026617147)
            ·
              refine ⟨17773460436618168039925721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11848973624412112026617147 17773460436618168039925721)
              ·
                refine ⟨13330095327463626029944291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17773460436618168039925721 13330095327463626029944291)
                ·
                  refine ⟨19995142991195439044916437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13330095327463626029944291 19995142991195439044916437)
                  ·
                    refine ⟨468636163856143102615229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19995142991195439044916437 468636163856143102615229)
                    ·
                      rfl

theorem cell23_2737997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_2737997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2737997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2737997 prefixEnd_2737997 := by exact prefixLift 2737997
  have htrace : WordTrace (prefixWord ++ tailWord_2737997) baseStart_2737997 baseEnd_2737997 := by
    simpa [prefixWord, tailWord_2737997, baseEnd_2737997] using wordTrace_append hprefix tailTrace_2737997
  have hstable : (prefixWord ++ tailWord_2737997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2737997).length < 2 ^ (prefixWord ++ tailWord_2737997).sum := by decide
  have hdescent : baseEnd_2737997 < baseStart_2737997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2737997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738127 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 3]
def baseStart_2738127 : Nat := 118140960795 + 2738127 * 2 ^ 59
def prefixEnd_2738127 : Nat := 4983230072969 + 3 ^ 40 * 2738127 * 2
def baseEnd_2738127 : Nat := 1405975244053513799220089

theorem tailTrace_2738127 : CollatzResearch.WordTrace tailWord_2738127 prefixEnd_2738127 1405975244053513799220089 := by
  unfold tailWord_2738127
  simp only [CollatzResearch.WordTrace]
  refine ⟨99867696151240988706396635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66578464100827325804264423 99867696151240988706396635)
  ·
    refine ⟨149801544226861483059594953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99867696151240988706396635 149801544226861483059594953)
    ·
      refine ⟨112351158170146112294696215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149801544226861483059594953 112351158170146112294696215)
      ·
        refine ⟨168526737255219168442044323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112351158170146112294696215 168526737255219168442044323)
        ·
          refine ⟨252790105882828752663066485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168526737255219168442044323 252790105882828752663066485)
          ·
            refine ⟨23699072426515195562162483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252790105882828752663066485 23699072426515195562162483)
            ·
              refine ⟨35548608639772793343243725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23699072426515195562162483 35548608639772793343243725)
              ·
                refine ⟨13330728239914797503716397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35548608639772793343243725 13330728239914797503716397)
                ·
                  refine ⟨4999023089968049063893649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13330728239914797503716397 4999023089968049063893649)
                  ·
                    refine ⟨3749267317476036797920237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4999023089968049063893649 3749267317476036797920237)
                    ·
                      refine ⟨1405975244053513799220089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3749267317476036797920237 1405975244053513799220089)
                      ·
                        rfl

theorem cell23_2738127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_2738127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738127 prefixEnd_2738127 := by exact prefixLift 2738127
  have htrace : WordTrace (prefixWord ++ tailWord_2738127) baseStart_2738127 baseEnd_2738127 := by
    simpa [prefixWord, tailWord_2738127, baseEnd_2738127] using wordTrace_append hprefix tailTrace_2738127
  have hstable : (prefixWord ++ tailWord_2738127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738127).length < 2 ^ (prefixWord ++ tailWord_2738127).sum := by decide
  have hdescent : baseEnd_2738127 < baseStart_2738127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738138 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_2738138 : Nat := 118140960795 + 2738138 * 2 ^ 59
def prefixEnd_2738138 : Nat := 4983230072969 + 3 ^ 40 * 2738138 * 2
def baseEnd_2738138 : Nat := 468660297446904418727513

theorem tailTrace_2738138 : CollatzResearch.WordTrace tailWord_2738138 prefixEnd_2738138 468660297446904418727513 := by
  unfold tailWord_2738138
  simp only [CollatzResearch.WordTrace]
  refine ⟨24967024338550284396261767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66578731569467425056698045 24967024338550284396261767)
  ·
    refine ⟨37450536507825426594392651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24967024338550284396261767 37450536507825426594392651)
    ·
      refine ⟨56175804761738139891588977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37450536507825426594392651 56175804761738139891588977)
      ·
        refine ⟨42131853571303604918691733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56175804761738139891588977 42131853571303604918691733)
        ·
          refine ⟨1974930636154856480563675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42131853571303604918691733 1974930636154856480563675)
          ·
            refine ⟨2962395954232284720845513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974930636154856480563675 2962395954232284720845513)
            ·
              refine ⟨2221796965674213540634135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2962395954232284720845513 2221796965674213540634135)
              ·
                refine ⟨3332695448511320310951203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221796965674213540634135 3332695448511320310951203)
                ·
                  refine ⟨4999043172766980466426805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332695448511320310951203 4999043172766980466426805)
                  ·
                    refine ⟨468660297446904418727513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4999043172766980466426805 468660297446904418727513)
                    ·
                      rfl

theorem cell23_2738138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_2738138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738138 prefixEnd_2738138 := by exact prefixLift 2738138
  have htrace : WordTrace (prefixWord ++ tailWord_2738138) baseStart_2738138 baseEnd_2738138 := by
    simpa [prefixWord, tailWord_2738138, baseEnd_2738138] using wordTrace_append hprefix tailTrace_2738138
  have hstable : (prefixWord ++ tailWord_2738138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738138).length < 2 ^ (prefixWord ++ tailWord_2738138).sum := by decide
  have hdescent : baseEnd_2738138 < baseStart_2738138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738141 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2738141 : Nat := 118140960795 + 2738141 * 2 ^ 59
def prefixEnd_2738141 : Nat := 4983230072969 + 3 ^ 40 * 2738141 * 2
def baseEnd_2738141 : Nat := 1405982432782676744445025

theorem tailTrace_2738141 : CollatzResearch.WordTrace tailWord_2738141 prefixEnd_2738141 1405982432782676744445025 := by
  unfold tailWord_2738141
  simp only [CollatzResearch.WordTrace]
  refine ⟨99868206773190269097406277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66578804515460179398270851 99868206773190269097406277)
  ·
    refine ⟨18725288769973175455763677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99868206773190269097406277 18725288769973175455763677)
    ·
      refine ⟨7021983288739940795911379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18725288769973175455763677 7021983288739940795911379)
      ·
        refine ⟨10532974933109911193867069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7021983288739940795911379 10532974933109911193867069)
        ·
          refine ⟨3949865599916216697700151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10532974933109911193867069 3949865599916216697700151)
          ·
            refine ⟨5924798399874325046550227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949865599916216697700151 5924798399874325046550227)
            ·
              refine ⟨8887197599811487569825341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5924798399874325046550227 8887197599811487569825341)
              ·
                refine ⟨3332699099929307838684503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8887197599811487569825341 3332699099929307838684503)
                ·
                  refine ⟨4999048649893961758026755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332699099929307838684503 4999048649893961758026755)
                  ·
                    refine ⟨7498572974840942637040133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4999048649893961758026755 7498572974840942637040133)
                    ·
                      refine ⟨1405982432782676744445025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7498572974840942637040133 1405982432782676744445025)
                      ·
                        rfl

theorem cell23_2738141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2738141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738141 prefixEnd_2738141 := by exact prefixLift 2738141
  have htrace : WordTrace (prefixWord ++ tailWord_2738141) baseStart_2738141 baseEnd_2738141 := by
    simpa [prefixWord, tailWord_2738141, baseEnd_2738141] using wordTrace_append hprefix tailTrace_2738141
  have hstable : (prefixWord ++ tailWord_2738141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738141).length < 2 ^ (prefixWord ++ tailWord_2738141).sum := by decide
  have hdescent : baseEnd_2738141 < baseStart_2738141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738158 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_2738158 : Nat := 118140960795 + 2738158 * 2 ^ 59
def prefixEnd_2738158 : Nat := 4983230072969 + 3 ^ 40 * 2738158 * 2
def baseEnd_2738158 : Nat := 1405991161953803177932447

theorem tailTrace_2738158 : CollatzResearch.WordTrace tailWord_2738158 prefixEnd_2738158 1405991161953803177932447 := by
  unfold tailWord_2738158
  simp only [CollatzResearch.WordTrace]
  refine ⟨12483603351766085125096891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66579217876085787333850085 12483603351766085125096891)
  ·
    refine ⟨18725405027649127687645337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12483603351766085125096891 18725405027649127687645337)
    ·
      refine ⟨14044053770736845765734003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18725405027649127687645337 14044053770736845765734003)
      ·
        refine ⟨21066080656105268648601005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14044053770736845765734003 21066080656105268648601005)
        ·
          refine ⟨7899780246039475743225377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21066080656105268648601005 7899780246039475743225377)
          ·
            refine ⟨5924835184529606807419033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7899780246039475743225377 5924835184529606807419033)
            ·
              refine ⟨4443626388397205105564275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5924835184529606807419033 4443626388397205105564275)
              ·
                refine ⟨6665439582595807658346413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4443626388397205105564275 6665439582595807658346413)
                ·
                  refine ⟨2499539843473427871879905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6665439582595807658346413 2499539843473427871879905)
                  ·
                    refine ⟨1874654882605070903909929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2499539843473427871879905 1874654882605070903909929)
                    ·
                      refine ⟨1405991161953803177932447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874654882605070903909929 1405991161953803177932447)
                      ·
                        rfl

theorem cell23_2738158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_2738158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738158 prefixEnd_2738158 := by exact prefixLift 2738158
  have htrace : WordTrace (prefixWord ++ tailWord_2738158) baseStart_2738158 baseEnd_2738158 := by
    simpa [prefixWord, tailWord_2738158, baseEnd_2738158] using wordTrace_append hprefix tailTrace_2738158
  have hstable : (prefixWord ++ tailWord_2738158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738158).length < 2 ^ (prefixWord ++ tailWord_2738158).sum := by decide
  have hdescent : baseEnd_2738158 < baseStart_2738158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738160 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 1, 9]
def baseStart_2738160 : Nat := 118140960795 + 2738160 * 2 ^ 59
def prefixEnd_2738160 : Nat := 4983230072969 + 3 ^ 40 * 2738160 * 2
def baseEnd_2738160 : Nat := 468664062971704056702479

theorem tailTrace_2738160 : CollatzResearch.WordTrace tailWord_2738160 prefixEnd_2738160 468664062971704056702479 := by
  unfold tailWord_2738160
  simp only [CollatzResearch.WordTrace]
  refine ⟨49934449880060717671173967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66579266506747623561565289 49934449880060717671173967)
  ·
    refine ⟨74901674820091076506760951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49934449880060717671173967 74901674820091076506760951)
    ·
      refine ⟨112352512230136614760141427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74901674820091076506760951 112352512230136614760141427)
      ·
        refine ⟨168528768345204922140212141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112352512230136614760141427 168528768345204922140212141)
        ·
          refine ⟨63198288129451845802579553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168528768345204922140212141 63198288129451845802579553)
          ·
            refine ⟨47398716097088884351934665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63198288129451845802579553 47398716097088884351934665)
            ·
              refine ⟨35549037072816663263950999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47398716097088884351934665 35549037072816663263950999)
              ·
                refine ⟨53323555609224994895926499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35549037072816663263950999 53323555609224994895926499)
                ·
                  refine ⟨79985333413837492343889749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53323555609224994895926499 79985333413837492343889749)
                  ·
                    refine ⟨468664062971704056702479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79985333413837492343889749 468664062971704056702479)
                    ·
                      rfl

theorem cell23_2738160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_2738160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738160 prefixEnd_2738160 := by exact prefixLift 2738160
  have htrace : WordTrace (prefixWord ++ tailWord_2738160) baseStart_2738160 baseEnd_2738160 := by
    simpa [prefixWord, tailWord_2738160, baseEnd_2738160] using wordTrace_append hprefix tailTrace_2738160
  have hstable : (prefixWord ++ tailWord_2738160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738160).length < 2 ^ (prefixWord ++ tailWord_2738160).sum := by decide
  have hdescent : baseEnd_2738160 < baseStart_2738160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738227 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 4]
def baseStart_2738227 : Nat := 118140960795 + 2738227 * 2 ^ 59
def prefixEnd_2738227 : Nat := 4983230072969 + 3 ^ 40 * 2738227 * 2
def baseEnd_2738227 : Nat := 1406026592118963407969629

theorem tailTrace_2738227 : CollatzResearch.WordTrace tailWord_2738227 prefixEnd_2738227 1406026592118963407969629 := by
  unfold tailWord_2738227
  simp only [CollatzResearch.WordTrace]
  refine ⟨99871343450878705785036935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66580895633919137190024623 99871343450878705785036935)
  ·
    refine ⟨149807015176318058677555403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99871343450878705785036935 149807015176318058677555403)
    ·
      refine ⟨224710522764477088016333105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149807015176318058677555403 224710522764477088016333105)
      ·
        refine ⟨168532892073357816012249829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224710522764477088016333105 168532892073357816012249829)
        ·
          refine ⟨31599917263754590502296843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168532892073357816012249829 31599917263754590502296843)
          ·
            refine ⟨47399875895631885753445265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31599917263754590502296843 47399875895631885753445265)
            ·
              refine ⟨35549906921723914315083949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47399875895631885753445265 35549906921723914315083949)
              ·
                refine ⟨13331215095646467868156481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35549906921723914315083949 13331215095646467868156481)
                ·
                  refine ⟨9998411321734850901117361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13331215095646467868156481 9998411321734850901117361)
                  ·
                    refine ⟨7498808491301138175838021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9998411321734850901117361 7498808491301138175838021)
                    ·
                      refine ⟨1406026592118963407969629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7498808491301138175838021 1406026592118963407969629)
                      ·
                        rfl

theorem cell23_2738227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_2738227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738227 prefixEnd_2738227 := by exact prefixLift 2738227
  have htrace : WordTrace (prefixWord ++ tailWord_2738227) baseStart_2738227 baseEnd_2738227 := by
    simpa [prefixWord, tailWord_2738227, baseEnd_2738227] using wordTrace_append hprefix tailTrace_2738227
  have hstable : (prefixWord ++ tailWord_2738227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738227).length < 2 ^ (prefixWord ++ tailWord_2738227).sum := by decide
  have hdescent : baseEnd_2738227 < baseStart_2738227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738237 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 9]
def baseStart_2738237 : Nat := 118140960795 + 2738237 * 2 ^ 59
def prefixEnd_2738237 : Nat := 4983230072969 + 3 ^ 40 * 2738237 * 2
def baseEnd_2738237 : Nat := 156225747436167596538287

theorem tailTrace_2738237 : CollatzResearch.WordTrace tailWord_2738237 prefixEnd_2738237 156225747436167596538287 := by
  unfold tailWord_2738237
  simp only [CollatzResearch.WordTrace]
  refine ⟨99871708180842477492900965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66581138787228318328600643 99871708180842477492900965)
  ·
    refine ⟨18725945283907964529918931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99871708180842477492900965 18725945283907964529918931)
    ·
      refine ⟨28088917925861946794878397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18725945283907964529918931 28088917925861946794878397)
      ·
        refine ⟨10533344222198230048079399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28088917925861946794878397 10533344222198230048079399)
        ·
          refine ⟨15800016333297345072119099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10533344222198230048079399 15800016333297345072119099)
          ·
            refine ⟨23700024499946017608178649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15800016333297345072119099 23700024499946017608178649)
            ·
              refine ⟨17775018374959513206133987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23700024499946017608178649 17775018374959513206133987)
              ·
                refine ⟨26662527562439269809200981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17775018374959513206133987 26662527562439269809200981)
                ·
                  refine ⟨156225747436167596538287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26662527562439269809200981 156225747436167596538287)
                  ·
                    rfl

theorem cell23_2738237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_2738237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738237 prefixEnd_2738237 := by exact prefixLift 2738237
  have htrace : WordTrace (prefixWord ++ tailWord_2738237) baseStart_2738237 baseEnd_2738237 := by
    simpa [prefixWord, tailWord_2738237, baseEnd_2738237] using wordTrace_append hprefix tailTrace_2738237
  have hstable : (prefixWord ++ tailWord_2738237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738237).length < 2 ^ (prefixWord ++ tailWord_2738237).sum := by decide
  have hdescent : baseEnd_2738237 < baseStart_2738237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738301 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_2738301 : Nat := 118140960795 + 2738301 * 2 ^ 59
def prefixEnd_2738301 : Nat := 4983230072969 + 3 ^ 40 * 2738301 * 2
def baseEnd_2738301 : Nat := 468688196562465372814763

theorem tailTrace_2738301 : CollatzResearch.WordTrace tailWord_2738301 prefixEnd_2738301 468688196562465372814763 := by
  unfold tailWord_2738301
  simp only [CollatzResearch.WordTrace]
  refine ⟨99874042452610616423230757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66582694968407077615487171 99874042452610616423230757)
  ·
    refine ⟨18726382959864490579355767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99874042452610616423230757 18726382959864490579355767)
    ·
      refine ⟨28089574439796735869033651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18726382959864490579355767 28089574439796735869033651)
      ·
        refine ⟨42134361659695103803550477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28089574439796735869033651 42134361659695103803550477)
        ·
          refine ⟨15800385622385663926331429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42134361659695103803550477 15800385622385663926331429)
          ·
            refine ⟨2962572304197311986187143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15800385622385663926331429 2962572304197311986187143)
            ·
              refine ⟨4443858456295967979280715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962572304197311986187143 4443858456295967979280715)
              ·
                refine ⟨6665787684443951968921073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4443858456295967979280715 6665787684443951968921073)
                ·
                  refine ⟨4999340763332963976690805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6665787684443951968921073 4999340763332963976690805)
                  ·
                    refine ⟨468688196562465372814763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4999340763332963976690805 468688196562465372814763)
                    ·
                      rfl

theorem cell23_2738301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_2738301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738301 prefixEnd_2738301 := by exact prefixLift 2738301
  have htrace : WordTrace (prefixWord ++ tailWord_2738301) baseStart_2738301 baseEnd_2738301 := by
    simpa [prefixWord, tailWord_2738301, baseEnd_2738301] using wordTrace_append hprefix tailTrace_2738301
  have hstable : (prefixWord ++ tailWord_2738301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738301).length < 2 ^ (prefixWord ++ tailWord_2738301).sum := by decide
  have hdescent : baseEnd_2738301 < baseStart_2738301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738304 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 3, 6, 2]
def baseStart_2738304 : Nat := 118140960795 + 2738304 * 2 ^ 59
def prefixEnd_2738304 : Nat := 4983230072969 + 3 ^ 40 * 2738304 * 2
def baseEnd_2738304 : Nat := 1406066130129359606706775

theorem tailTrace_2738304 : CollatzResearch.WordTrace tailWord_2738304 prefixEnd_2738304 1406066130129359606706775 := by
  unfold tailWord_2738304
  simp only [CollatzResearch.WordTrace]
  refine ⟨49937075935799873967794983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66582767914399831957059977 49937075935799873967794983)
  ·
    refine ⟨74905613903699810951692475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49937075935799873967794983 74905613903699810951692475)
    ·
      refine ⟨112358420855549716427538713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74905613903699810951692475 112358420855549716427538713)
      ·
        refine ⟨84268815641662287320654035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112358420855549716427538713 84268815641662287320654035)
        ·
          refine ⟨126403223462493430980981053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84268815641662287320654035 126403223462493430980981053)
          ·
            refine ⟨47401208798435036617867895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126403223462493430980981053 47401208798435036617867895)
            ·
              refine ⟨71101813197652554926801843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47401208798435036617867895 71101813197652554926801843)
              ·
                refine ⟨106652719796478832390202765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71101813197652554926801843 106652719796478832390202765)
                ·
                  refine ⟨39994769923679562146326037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106652719796478832390202765 39994769923679562146326037)
                  ·
                    refine ⟨1874754840172479475609033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39994769923679562146326037 1874754840172479475609033)
                    ·
                      refine ⟨1406066130129359606706775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874754840172479475609033 1406066130129359606706775)
                      ·
                        rfl

theorem cell23_2738304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_2738304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738304 prefixEnd_2738304 := by exact prefixLift 2738304
  have htrace : WordTrace (prefixWord ++ tailWord_2738304) baseStart_2738304 baseEnd_2738304 := by
    simpa [prefixWord, tailWord_2738304, baseEnd_2738304] using wordTrace_append hprefix tailTrace_2738304
  have hstable : (prefixWord ++ tailWord_2738304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738304).length < 2 ^ (prefixWord ++ tailWord_2738304).sum := by decide
  have hdescent : baseEnd_2738304 < baseStart_2738304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738331 : List Nat := [1, 1, 1, 1, 1, 1, 2, 10, 1, 4]
def baseStart_2738331 : Nat := 118140960795 + 2738331 * 2 ^ 59
def prefixEnd_2738331 : Nat := 4983230072969 + 3 ^ 40 * 2738331 * 2
def baseEnd_2738331 : Nat := 468693331369010333689717

theorem tailTrace_2738331 : CollatzResearch.WordTrace tailWord_2738331 prefixEnd_2738331 468693331369010333689717 := by
  unfold tailWord_2738331
  simp only [CollatzResearch.WordTrace]
  refine ⟨99875136642501931546822847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66583424428334621031215231 99875136642501931546822847)
  ·
    refine ⟨149812704963752897320234271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99875136642501931546822847 149812704963752897320234271)
    ·
      refine ⟨224719057445629345980351407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149812704963752897320234271 224719057445629345980351407)
      ·
        refine ⟨337078586168444018970527111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224719057445629345980351407 337078586168444018970527111)
        ·
          refine ⟨505617879252666028455790667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337078586168444018970527111 505617879252666028455790667)
          ·
            refine ⟨758426818878999042683686001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505617879252666028455790667 758426818878999042683686001)
            ·
              refine ⟨568820114159249282012764501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758426818878999042683686001 568820114159249282012764501)
              ·
                refine ⟨1666465178200925630896771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 568820114159249282012764501 1666465178200925630896771)
                ·
                  refine ⟨2499697767301388446345157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666465178200925630896771 2499697767301388446345157)
                  ·
                    refine ⟨468693331369010333689717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2499697767301388446345157 468693331369010333689717)
                    ·
                      rfl

theorem cell23_2738331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 4].length) (baseStart_2738331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738331 prefixEnd_2738331 := by exact prefixLift 2738331
  have htrace : WordTrace (prefixWord ++ tailWord_2738331) baseStart_2738331 baseEnd_2738331 := by
    simpa [prefixWord, tailWord_2738331, baseEnd_2738331] using wordTrace_append hprefix tailTrace_2738331
  have hstable : (prefixWord ++ tailWord_2738331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738331).length < 2 ^ (prefixWord ++ tailWord_2738331).sum := by decide
  have hdescent : baseEnd_2738331 < baseStart_2738331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738338 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_2738338 : Nat := 118140960795 + 2738338 * 2 ^ 59
def prefixEnd_2738338 : Nat := 4983230072969 + 3 ^ 40 * 2738338 * 2
def baseEnd_2738338 : Nat := 1406083588471612473681619

theorem tailTrace_2738338 : CollatzResearch.WordTrace tailWord_2738338 prefixEnd_2738338 1406083588471612473681619 := by
  unfold tailWord_2738338
  simp only [CollatzResearch.WordTrace]
  refine ⟨24968847988369142935581917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66583594635651047828218445 24968847988369142935581917)
  ·
    refine ⟨9363317995638428600843219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24968847988369142935581917 9363317995638428600843219)
    ·
      refine ⟨14044976993457642901264829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9363317995638428600843219 14044976993457642901264829)
      ·
        refine ⟨5266866372546616087974311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14044976993457642901264829 5266866372546616087974311)
        ·
          refine ⟨7900299558819924131961467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5266866372546616087974311 7900299558819924131961467)
          ·
            refine ⟨11850449338229886197942201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7900299558819924131961467 11850449338229886197942201)
            ·
              refine ⟨8887837003672414648456651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11850449338229886197942201 8887837003672414648456651)
              ·
                refine ⟨13331755505508621972684977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8887837003672414648456651 13331755505508621972684977)
                ·
                  refine ⟨9998816629131466479513733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13331755505508621972684977 9998816629131466479513733)
                  ·
                    refine ⟨1874778117962149964908825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9998816629131466479513733 1874778117962149964908825)
                    ·
                      refine ⟨1406083588471612473681619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874778117962149964908825 1406083588471612473681619)
                      ·
                        rfl

theorem cell23_2738338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_2738338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738338 prefixEnd_2738338 := by exact prefixLift 2738338
  have htrace : WordTrace (prefixWord ++ tailWord_2738338) baseStart_2738338 baseEnd_2738338 := by
    simpa [prefixWord, tailWord_2738338, baseEnd_2738338] using wordTrace_append hprefix tailTrace_2738338
  have hstable : (prefixWord ++ tailWord_2738338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738338).length < 2 ^ (prefixWord ++ tailWord_2738338).sum := by decide
  have hdescent : baseEnd_2738338 < baseStart_2738338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738354 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_2738354 : Nat := 118140960795 + 2738354 * 2 ^ 59
def prefixEnd_2738354 : Nat := 4983230072969 + 3 ^ 40 * 2738354 * 2
def baseEnd_2738354 : Nat := 1406091804162084411081545

theorem tailTrace_2738354 : CollatzResearch.WordTrace tailWord_2738354 prefixEnd_2738354 1406091804162084411081545 := by
  unfold tailWord_2738354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24968993880354651618727529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66583983680945737649940077 24968993880354651618727529)
  ·
    refine ⟨18726745410265988714045647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24968993880354651618727529 18726745410265988714045647)
    ·
      refine ⟨28090118115398983071068471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18726745410265988714045647 28090118115398983071068471)
      ·
        refine ⟨42135177173098474606602707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28090118115398983071068471 42135177173098474606602707)
        ·
          refine ⟨63202765759647711909904061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42135177173098474606602707 63202765759647711909904061)
          ·
            refine ⟨23701037159867891966214023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63202765759647711909904061 23701037159867891966214023)
            ·
              refine ⟨35551555739801837949321035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23701037159867891966214023 35551555739801837949321035)
              ·
                refine ⟨53327333609702756923981553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35551555739801837949321035 53327333609702756923981553)
                ·
                  refine ⟨39995500207277067692986165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53327333609702756923981553 39995500207277067692986165)
                  ·
                    refine ⟨3749578144432225096217453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39995500207277067692986165 3749578144432225096217453)
                    ·
                      refine ⟨1406091804162084411081545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3749578144432225096217453 1406091804162084411081545)
                      ·
                        rfl

theorem cell23_2738354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_2738354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738354 prefixEnd_2738354 := by exact prefixLift 2738354
  have htrace : WordTrace (prefixWord ++ tailWord_2738354) baseStart_2738354 baseEnd_2738354 := by
    simpa [prefixWord, tailWord_2738354, baseEnd_2738354] using wordTrace_append hprefix tailTrace_2738354
  have hstable : (prefixWord ++ tailWord_2738354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738354).length < 2 ^ (prefixWord ++ tailWord_2738354).sum := by decide
  have hdescent : baseEnd_2738354 < baseStart_2738354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738387 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 2, 10]
def baseStart_2738387 : Nat := 118140960795 + 2738387 * 2 ^ 59
def prefixEnd_2738387 : Nat := 4983230072969 + 3 ^ 40 * 2738387 * 2
def baseEnd_2738387 : Nat := 468702916341227593989631

theorem tailTrace_2738387 : CollatzResearch.WordTrace tailWord_2738387 prefixEnd_2738387 468702916341227593989631 := by
  unfold tailWord_2738387
  simp only [CollatzResearch.WordTrace]
  refine ⟨99877179130299053110861415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66584786086866035407240943 99877179130299053110861415)
  ·
    refine ⟨149815768695448579666292123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99877179130299053110861415 149815768695448579666292123)
    ·
      refine ⟨224723653043172869499438185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149815768695448579666292123 224723653043172869499438185)
      ·
        refine ⟨168542739782379652124578639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224723653043172869499438185 168542739782379652124578639)
        ·
          refine ⟨252814109673569478186867959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168542739782379652124578639 252814109673569478186867959)
          ·
            refine ⟨379221164510354217280301939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252814109673569478186867959 379221164510354217280301939)
            ·
              refine ⟨568831746765531325920452909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379221164510354217280301939 568831746765531325920452909)
              ·
                refine ⟨213311905037074247220169841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 568831746765531325920452909 213311905037074247220169841)
                ·
                  refine ⟨159983928777805685415127381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213311905037074247220169841 159983928777805685415127381)
                  ·
                    refine ⟨468702916341227593989631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 159983928777805685415127381 468702916341227593989631)
                    ·
                      rfl

theorem cell23_2738387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 10].length) (baseStart_2738387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738387 prefixEnd_2738387 := by exact prefixLift 2738387
  have htrace : WordTrace (prefixWord ++ tailWord_2738387) baseStart_2738387 baseEnd_2738387 := by
    simpa [prefixWord, tailWord_2738387, baseEnd_2738387] using wordTrace_append hprefix tailTrace_2738387
  have hstable : (prefixWord ++ tailWord_2738387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738387).length < 2 ^ (prefixWord ++ tailWord_2738387).sum := by decide
  have hdescent : baseEnd_2738387 < baseStart_2738387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738404 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_2738404 : Nat := 118140960795 + 2738404 * 2 ^ 59
def prefixEnd_2738404 : Nat := 4983230072969 + 3 ^ 40 * 2738404 * 2
def baseEnd_2738404 : Nat := 468705826064936405152105

theorem tailTrace_2738404 : CollatzResearch.WordTrace tailWord_2738404 prefixEnd_2738404 468705826064936405152105 := by
  unfold tailWord_2738404
  simp only [CollatzResearch.WordTrace]
  refine ⟨49938899585618732507115133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66585199447491643342820177 49938899585618732507115133)
  ·
    refine ⟨18727087344607024690168175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49938899585618732507115133 18727087344607024690168175)
    ·
      refine ⟨28090631016910537035252263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18727087344607024690168175 28090631016910537035252263)
      ·
        refine ⟨42135946525365805552878395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28090631016910537035252263 42135946525365805552878395)
        ·
          refine ⟨63203919788048708329317593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42135946525365805552878395 63203919788048708329317593)
          ·
            refine ⟨47402939841036531246988195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63203919788048708329317593 47402939841036531246988195)
            ·
              refine ⟨71104409761554796870482293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47402939841036531246988195 71104409761554796870482293)
              ·
                refine ⟨6666038415145762206607715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71104409761554796870482293 6666038415145762206607715)
                ·
                  refine ⟨9999057622718643309911573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6666038415145762206607715 9999057622718643309911573)
                  ·
                    refine ⟨468705826064936405152105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9999057622718643309911573 468705826064936405152105)
                    ·
                      rfl

theorem cell23_2738404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_2738404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738404 prefixEnd_2738404 := by exact prefixLift 2738404
  have htrace : WordTrace (prefixWord ++ tailWord_2738404) baseStart_2738404 baseEnd_2738404 := by
    simpa [prefixWord, tailWord_2738404, baseEnd_2738404] using wordTrace_append hprefix tailTrace_2738404
  have hstable : (prefixWord ++ tailWord_2738404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738404).length < 2 ^ (prefixWord ++ tailWord_2738404).sum := by decide
  have hdescent : baseEnd_2738404 < baseStart_2738404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738408 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 1, 5]
def baseStart_2738408 : Nat := 118140960795 + 2738408 * 2 ^ 59
def prefixEnd_2738408 : Nat := 4983230072969 + 3 ^ 40 * 2738408 * 2
def baseEnd_2738408 : Nat := 468706510705809066602099

theorem tailTrace_2738408 : CollatzResearch.WordTrace tailWord_2738408 prefixEnd_2738408 468706510705809066602099 := by
  unfold tailWord_2738408
  simp only [CollatzResearch.WordTrace]
  refine ⟨49938972531611486848687939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66585296708815315798250585 49938972531611486848687939)
  ·
    refine ⟨74908458797417230273031909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49938972531611486848687939 74908458797417230273031909)
    ·
      refine ⟨14045336024515730676193483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74908458797417230273031909 14045336024515730676193483)
      ·
        refine ⟨21068004036773596014290225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14045336024515730676193483 21068004036773596014290225)
        ·
          refine ⟨15801003027580197010717669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21068004036773596014290225 15801003027580197010717669)
          ·
            refine ⟨2962688067671286939509563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15801003027580197010717669 2962688067671286939509563)
            ·
              refine ⟨4444032101506930409264345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962688067671286939509563 4444032101506930409264345)
              ·
                refine ⟨3333024076130197806948259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4444032101506930409264345 3333024076130197806948259)
                ·
                  refine ⟨4999536114195296710422389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333024076130197806948259 4999536114195296710422389)
                  ·
                    refine ⟨468706510705809066602099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4999536114195296710422389 468706510705809066602099)
                    ·
                      rfl

theorem cell23_2738408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_2738408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738408 prefixEnd_2738408 := by exact prefixLift 2738408
  have htrace : WordTrace (prefixWord ++ tailWord_2738408) baseStart_2738408 baseEnd_2738408 := by
    simpa [prefixWord, tailWord_2738408, baseEnd_2738408] using wordTrace_append hprefix tailTrace_2738408
  have hstable : (prefixWord ++ tailWord_2738408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738408).length < 2 ^ (prefixWord ++ tailWord_2738408).sum := by decide
  have hdescent : baseEnd_2738408 < baseStart_2738408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738458 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_2738458 : Nat := 118140960795 + 2738458 * 2 ^ 59
def prefixEnd_2738458 : Nat := 4983230072969 + 3 ^ 40 * 2738458 * 2
def baseEnd_2738458 : Nat := 1406145206150152004181067

theorem tailTrace_2738458 : CollatzResearch.WordTrace tailWord_2738458 prefixEnd_2738458 1406145206150152004181067 := by
  unfold tailWord_2738458
  simp only [CollatzResearch.WordTrace]
  refine ⟨24969942178260458059174007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66586512475361221491130685 24969942178260458059174007)
  ·
    refine ⟨37454913267390687088761011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24969942178260458059174007 37454913267390687088761011)
    ·
      refine ⟨56182369901086030633141517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37454913267390687088761011 56182369901086030633141517)
      ·
        refine ⟨21068388712907261487428069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56182369901086030633141517 21068388712907261487428069)
        ·
          refine ⟨3950322883670111528892763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21068388712907261487428069 3950322883670111528892763)
          ·
            refine ⟨5925484325505167293339145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3950322883670111528892763 5925484325505167293339145)
            ·
              refine ⟨4444113244128875470004359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5925484325505167293339145 4444113244128875470004359)
              ·
                refine ⟨6666169866193313205006539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4444113244128875470004359 6666169866193313205006539)
                ·
                  refine ⟨9999254799289969807509809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6666169866193313205006539 9999254799289969807509809)
                  ·
                    refine ⟨7499441099467477355632357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9999254799289969807509809 7499441099467477355632357)
                    ·
                      refine ⟨1406145206150152004181067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7499441099467477355632357 1406145206150152004181067)
                      ·
                        rfl

theorem cell23_2738458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_2738458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738458 prefixEnd_2738458 := by exact prefixLift 2738458
  have htrace : WordTrace (prefixWord ++ tailWord_2738458) baseStart_2738458 baseEnd_2738458 := by
    simpa [prefixWord, tailWord_2738458, baseEnd_2738458] using wordTrace_append hprefix tailTrace_2738458
  have hstable : (prefixWord ++ tailWord_2738458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738458).length < 2 ^ (prefixWord ++ tailWord_2738458).sum := by decide
  have hdescent : baseEnd_2738458 < baseStart_2738458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738462 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_2738462 : Nat := 118140960795 + 2738462 * 2 ^ 59
def prefixEnd_2738462 : Nat := 4983230072969 + 3 ^ 40 * 2738462 * 2
def baseEnd_2738462 : Nat := 1406147260072769988531049

theorem tailTrace_2738462 : CollatzResearch.WordTrace tailWord_2738462 prefixEnd_2738462 1406147260072769988531049 := by
  unfold tailWord_2738462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12484989325628417614980205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66586609736684893946561093 12484989325628417614980205)
  ·
    refine ⟨4681870997110656605617577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12484989325628417614980205 4681870997110656605617577)
    ·
      refine ⟨3511403247832992454213183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4681870997110656605617577 3511403247832992454213183)
      ·
        refine ⟨5267104871749488681319775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3511403247832992454213183 5267104871749488681319775)
        ·
          refine ⟨7900657307624233021979663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267104871749488681319775 7900657307624233021979663)
          ·
            refine ⟨11850985961436349532969495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7900657307624233021979663 11850985961436349532969495)
            ·
              refine ⟨17776478942154524299454243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11850985961436349532969495 17776478942154524299454243)
              ·
                refine ⟨26664718413231786449181365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17776478942154524299454243 26664718413231786449181365)
                ·
                  refine ⟨2499817351240479979610753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26664718413231786449181365 2499817351240479979610753)
                  ·
                    refine ⟨1874863013430359984708065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2499817351240479979610753 1874863013430359984708065)
                    ·
                      refine ⟨1406147260072769988531049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874863013430359984708065 1406147260072769988531049)
                      ·
                        rfl

theorem cell23_2738462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_2738462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738462 prefixEnd_2738462 := by exact prefixLift 2738462
  have htrace : WordTrace (prefixWord ++ tailWord_2738462) baseStart_2738462 baseEnd_2738462 := by
    simpa [prefixWord, tailWord_2738462, baseEnd_2738462] using wordTrace_append hprefix tailTrace_2738462
  have hstable : (prefixWord ++ tailWord_2738462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738462).length < 2 ^ (prefixWord ++ tailWord_2738462).sum := by decide
  have hdescent : baseEnd_2738462 < baseStart_2738462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738482 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_2738482 : Nat := 118140960795 + 2738482 * 2 ^ 59
def prefixEnd_2738482 : Nat := 4983230072969 + 3 ^ 40 * 2738482 * 2
def baseEnd_2738482 : Nat := 1406157529685859910280957

theorem tailTrace_2738482 : CollatzResearch.WordTrace tailWord_2738482 prefixEnd_2738482 1406157529685859910280957 := by
  unfold tailWord_2738482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24970161016238721083892425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66587096043303256223713133 24970161016238721083892425)
  ·
    refine ⟨18727620762179040812919319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24970161016238721083892425 18727620762179040812919319)
    ·
      refine ⟨28091431143268561219378979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18727620762179040812919319 28091431143268561219378979)
      ·
        refine ⟨42137146714902841829068469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28091431143268561219378979 42137146714902841829068469)
        ·
          refine ⟨3950357504522141421475169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42137146714902841829068469 3950357504522141421475169)
          ·
            refine ⟨2962768128391606066106377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3950357504522141421475169 2962768128391606066106377)
            ·
              refine ⟨2222076096293704549579783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2962768128391606066106377 2222076096293704549579783)
              ·
                refine ⟨3333114144440556824369675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222076096293704549579783 3333114144440556824369675)
                ·
                  refine ⟨4999671216660835236554513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333114144440556824369675 4999671216660835236554513)
                  ·
                    refine ⟨3749753412495626427415885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4999671216660835236554513 3749753412495626427415885)
                    ·
                      refine ⟨1406157529685859910280957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3749753412495626427415885 1406157529685859910280957)
                      ·
                        rfl

theorem cell23_2738482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_2738482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738482 prefixEnd_2738482 := by exact prefixLift 2738482
  have htrace : WordTrace (prefixWord ++ tailWord_2738482) baseStart_2738482 baseEnd_2738482 := by
    simpa [prefixWord, tailWord_2738482, baseEnd_2738482] using wordTrace_append hprefix tailTrace_2738482
  have hstable : (prefixWord ++ tailWord_2738482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738482).length < 2 ^ (prefixWord ++ tailWord_2738482).sum := by decide
  have hdescent : baseEnd_2738482 < baseStart_2738482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738501 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 2, 8, 2]
def baseStart_2738501 : Nat := 118140960795 + 2738501 * 2 ^ 59
def prefixEnd_2738501 : Nat := 4983230072969 + 3 ^ 40 * 2738501 * 2
def baseEnd_2738501 : Nat := 1406167285818295335943369

theorem tailTrace_2738501 : CollatzResearch.WordTrace tailWord_2738501 prefixEnd_2738501 1406167285818295335943369 := by
  unfold tailWord_2738501
  simp only [CollatzResearch.WordTrace]
  refine ⟨99881337051886050580511357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66587558034590700387007571 99881337051886050580511357)
  ·
    refine ⟨37455501394457268967691759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99881337051886050580511357 37455501394457268967691759)
    ·
      refine ⟨56183252091685903451537639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37455501394457268967691759 56183252091685903451537639)
      ·
        refine ⟨84274878137528855177306459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56183252091685903451537639 84274878137528855177306459)
        ·
          refine ⟨126412317206293282765959689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84274878137528855177306459 126412317206293282765959689)
          ·
            refine ⟨94809237904719962074469767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126412317206293282765959689 94809237904719962074469767)
            ·
              refine ⟨142213856857079943111704651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94809237904719962074469767 142213856857079943111704651)
              ·
                refine ⟨213320785285619914667556977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142213856857079943111704651 213320785285619914667556977)
                ·
                  refine ⟨159990588964214936000667733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213320785285619914667556977 159990588964214936000667733)
                  ·
                    refine ⟨1874889714424393781257825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 159990588964214936000667733 1874889714424393781257825)
                    ·
                      refine ⟨1406167285818295335943369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874889714424393781257825 1406167285818295335943369)
                      ·
                        rfl

theorem cell23_2738501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_2738501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738501 prefixEnd_2738501 := by exact prefixLift 2738501
  have htrace : WordTrace (prefixWord ++ tailWord_2738501) baseStart_2738501 baseEnd_2738501 := by
    simpa [prefixWord, tailWord_2738501, baseEnd_2738501] using wordTrace_append hprefix tailTrace_2738501
  have hstable : (prefixWord ++ tailWord_2738501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738501).length < 2 ^ (prefixWord ++ tailWord_2738501).sum := by decide
  have hdescent : baseEnd_2738501 < baseStart_2738501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738535 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_2738535 : Nat := 118140960795 + 2738535 * 2 ^ 59
def prefixEnd_2738535 : Nat := 4983230072969 + 3 ^ 40 * 2738535 * 2
def baseEnd_2738535 : Nat := 1406184744160548202918213

theorem tailTrace_2738535 : CollatzResearch.WordTrace tailWord_2738535 prefixEnd_2738535 1406184744160548202918213 := by
  unfold tailWord_2738535
  simp only [CollatzResearch.WordTrace]
  refine ⟨99882577133762874387249059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66588384755841916258166039 99882577133762874387249059)
  ·
    refine ⟨149823865700644311580873589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99882577133762874387249059 149823865700644311580873589)
    ·
      refine ⟨14045987409435404210706899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149823865700644311580873589 14045987409435404210706899)
      ·
        refine ⟨21068981114153106316060349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14045987409435404210706899 21068981114153106316060349)
        ·
          refine ⟨7900867917807414868522631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21068981114153106316060349 7900867917807414868522631)
          ·
            refine ⟨11851301876711122302783947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7900867917807414868522631 11851301876711122302783947)
            ·
              refine ⟨17776952815066683454175921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11851301876711122302783947 17776952815066683454175921)
              ·
                refine ⟨13332714611300012590631941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17776952815066683454175921 13332714611300012590631941)
                ·
                  refine ⟨2499883989618752360743489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13332714611300012590631941 2499883989618752360743489)
                  ·
                    refine ⟨1874912992214064270557617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2499883989618752360743489 1874912992214064270557617)
                    ·
                      refine ⟨1406184744160548202918213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874912992214064270557617 1406184744160548202918213)
                      ·
                        rfl

theorem cell23_2738535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_2738535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738535 prefixEnd_2738535 := by exact prefixLift 2738535
  have htrace : WordTrace (prefixWord ++ tailWord_2738535) baseStart_2738535 baseEnd_2738535 := by
    simpa [prefixWord, tailWord_2738535, baseEnd_2738535] using wordTrace_append hprefix tailTrace_2738535
  have hstable : (prefixWord ++ tailWord_2738535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738535).length < 2 ^ (prefixWord ++ tailWord_2738535).sum := by decide
  have hdescent : baseEnd_2738535 < baseStart_2738535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738538 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2738538 : Nat := 118140960795 + 2738538 * 2 ^ 59
def prefixEnd_2738538 : Nat := 4983230072969 + 3 ^ 40 * 2738538 * 2
def baseEnd_2738538 : Nat := 1406186284602511691180699

theorem tailTrace_2738538 : CollatzResearch.WordTrace tailWord_2738538 prefixEnd_2738538 1406186284602511691180699 := by
  unfold tailWord_2738538
  simp only [CollatzResearch.WordTrace]
  refine ⟨24970671638188001474902067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66588457701834670599738845 24970671638188001474902067)
  ·
    refine ⟨37456007457282002212353101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24970671638188001474902067 37456007457282002212353101)
    ·
      refine ⟨14046002796480750829632413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37456007457282002212353101 14046002796480750829632413)
      ·
        refine ⟨5267251048680281561112155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14046002796480750829632413 5267251048680281561112155)
        ·
          refine ⟨7900876573020422341668233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267251048680281561112155 7900876573020422341668233)
          ·
            refine ⟨5925657429765316756251175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7900876573020422341668233 5925657429765316756251175)
            ·
              refine ⟨8888486144647975134376763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5925657429765316756251175 8888486144647975134376763)
              ·
                refine ⟨13332729216971962701565145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8888486144647975134376763 13332729216971962701565145)
                ·
                  refine ⟨9999546912728972026173859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13332729216971962701565145 9999546912728972026173859)
                  ·
                    refine ⟨14999320369093458039260789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9999546912728972026173859 14999320369093458039260789)
                    ·
                      refine ⟨1406186284602511691180699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14999320369093458039260789 1406186284602511691180699)
                      ·
                        rfl

theorem cell23_2738538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2738538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738538 prefixEnd_2738538 := by exact prefixLift 2738538
  have htrace : WordTrace (prefixWord ++ tailWord_2738538) baseStart_2738538 baseEnd_2738538 := by
    simpa [prefixWord, tailWord_2738538, baseEnd_2738538] using wordTrace_append hprefix tailTrace_2738538
  have hstable : (prefixWord ++ tailWord_2738538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738538).length < 2 ^ (prefixWord ++ tailWord_2738538).sum := by decide
  have hdescent : baseEnd_2738538 < baseStart_2738538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738551 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_2738551 : Nat := 118140960795 + 2738551 * 2 ^ 59
def prefixEnd_2738551 : Nat := 4983230072969 + 3 ^ 40 * 2738551 * 2
def baseEnd_2738551 : Nat := 1406192959851020140318139

theorem tailTrace_2738551 : CollatzResearch.WordTrace tailWord_2738551 prefixEnd_2738551 1406192959851020140318139 := by
  unfold tailWord_2738551
  simp only [CollatzResearch.WordTrace]
  refine ⟨99883160701704909119831507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66588773801136606079887671 99883160701704909119831507)
  ·
    refine ⟨149824741052557363679747261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99883160701704909119831507 149824741052557363679747261)
    ·
      refine ⟨56184277894709011379905223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149824741052557363679747261 56184277894709011379905223)
      ·
        refine ⟨84276416842063517069857835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56184277894709011379905223 84276416842063517069857835)
        ·
          refine ⟨126414625263095275604786753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84276416842063517069857835 126414625263095275604786753)
          ·
            refine ⟨94810968947321456703590065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126414625263095275604786753 94810968947321456703590065)
            ·
              refine ⟨71108226710491092527692549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94810968947321456703590065 71108226710491092527692549)
              ·
                refine ⟨13332792508217079848942353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71108226710491092527692549 13332792508217079848942353)
                ·
                  refine ⟨9999594381162809886706765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13332792508217079848942353 9999594381162809886706765)
                  ·
                    refine ⟨3749847892936053707515037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9999594381162809886706765 3749847892936053707515037)
                    ·
                      refine ⟨1406192959851020140318139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3749847892936053707515037 1406192959851020140318139)
                      ·
                        rfl

theorem cell23_2738551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_2738551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738551 prefixEnd_2738551 := by exact prefixLift 2738551
  have htrace : WordTrace (prefixWord ++ tailWord_2738551) baseStart_2738551 baseEnd_2738551 := by
    simpa [prefixWord, tailWord_2738551, baseEnd_2738551] using wordTrace_append hprefix tailTrace_2738551
  have hstable : (prefixWord ++ tailWord_2738551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738551).length < 2 ^ (prefixWord ++ tailWord_2738551).sum := by decide
  have hdescent : baseEnd_2738551 < baseStart_2738551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738569 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 2, 2, 2]
def baseStart_2738569 : Nat := 118140960795 + 2738569 * 2 ^ 59
def prefixEnd_2738569 : Nat := 4983230072969 + 3 ^ 40 * 2738569 * 2
def baseEnd_2738569 : Nat := 1406202202502801069893057

theorem tailTrace_2738569 : CollatzResearch.WordTrace tailWord_2738569 prefixEnd_2738569 1406202202502801069893057 := by
  unfold tailWord_2738569
  simp only [CollatzResearch.WordTrace]
  refine ⟨99883817215639698193986761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66589211477093132129324507 99883817215639698193986761)
  ·
    refine ⟨74912862911729773645490071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99883817215639698193986761 74912862911729773645490071)
    ·
      refine ⟨112369294367594660468235107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74912862911729773645490071 112369294367594660468235107)
      ·
        refine ⟨168553941551391990702352661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112369294367594660468235107 168553941551391990702352661)
        ·
          refine ⟨7900966010221499564172781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 168553941551391990702352661 7900966010221499564172781)
          ·
            refine ⟨2962862253833062336564793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7900966010221499564172781 2962862253833062336564793)
            ·
              refine ⟨2222146690374796752423595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2962862253833062336564793 2222146690374796752423595)
              ·
                refine ⟨3333220035562195128635393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222146690374796752423595 3333220035562195128635393)
                ·
                  refine ⟨2499915026671646346476545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3333220035562195128635393 2499915026671646346476545)
                  ·
                    refine ⟨1874936270003734759857409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2499915026671646346476545 1874936270003734759857409)
                    ·
                      refine ⟨1406202202502801069893057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1874936270003734759857409 1406202202502801069893057)
                      ·
                        rfl

theorem cell23_2738569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 2, 2].length) (baseStart_2738569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738569 prefixEnd_2738569 := by exact prefixLift 2738569
  have htrace : WordTrace (prefixWord ++ tailWord_2738569) baseStart_2738569 baseEnd_2738569 := by
    simpa [prefixWord, tailWord_2738569, baseEnd_2738569] using wordTrace_append hprefix tailTrace_2738569
  have hstable : (prefixWord ++ tailWord_2738569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738569).length < 2 ^ (prefixWord ++ tailWord_2738569).sum := by decide
  have hdescent : baseEnd_2738569 < baseStart_2738569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738611 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 3]
def baseStart_2738611 : Nat := 118140960795 + 2738611 * 2 ^ 59
def prefixEnd_2738611 : Nat := 4983230072969 + 3 ^ 40 * 2738611 * 2
def baseEnd_2738611 : Nat := 1406223768690289905567863

theorem tailTrace_2738611 : CollatzResearch.WordTrace tailWord_2738611 prefixEnd_2738611 1406223768690289905567863 := by
  unfold tailWord_2738611
  simp only [CollatzResearch.WordTrace]
  refine ⟨99885349081487539367015687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66590232720991692911343791 99885349081487539367015687)
  ·
    refine ⟨149828023622231309050523531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99885349081487539367015687 149828023622231309050523531)
    ·
      refine ⟨224742035433346963575785297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149828023622231309050523531 224742035433346963575785297)
      ·
        refine ⟨168556526575010222681838973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224742035433346963575785297 168556526575010222681838973)
        ·
          refine ⟨63208697465628833505689615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168556526575010222681838973 63208697465628833505689615)
          ·
            refine ⟨94813046198443250258534423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63208697465628833505689615 94813046198443250258534423)
            ·
              refine ⟨142219569297664875387801635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94813046198443250258534423 142219569297664875387801635)
              ·
                refine ⟨213329353946497313081702453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142219569297664875387801635 213329353946497313081702453)
                ·
                  refine ⟨19999626932484123101409605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213329353946497313081702453 19999626932484123101409605)
                  ·
                    refine ⟨3749930049840773081514301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19999626932484123101409605 3749930049840773081514301)
                    ·
                      refine ⟨1406223768690289905567863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3749930049840773081514301 1406223768690289905567863)
                      ·
                        rfl

theorem cell23_2738611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_2738611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738611 prefixEnd_2738611 := by exact prefixLift 2738611
  have htrace : WordTrace (prefixWord ++ tailWord_2738611) baseStart_2738611 baseEnd_2738611 := by
    simpa [prefixWord, tailWord_2738611, baseEnd_2738611] using wordTrace_append hprefix tailTrace_2738611
  have hstable : (prefixWord ++ tailWord_2738611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738611).length < 2 ^ (prefixWord ++ tailWord_2738611).sum := by decide
  have hdescent : baseEnd_2738611 < baseStart_2738611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738645 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2738645 : Nat := 118140960795 + 2738645 * 2 ^ 59
def prefixEnd_2738645 : Nat := 4983230072969 + 3 ^ 40 * 2738645 * 2
def baseEnd_2738645 : Nat := 1406241227032542772542707

theorem tailTrace_2738645 : CollatzResearch.WordTrace tailWord_2738645 prefixEnd_2738645 1406241227032542772542707 := by
  unfold tailWord_2738645
  simp only [CollatzResearch.WordTrace]
  refine ⟨99886589163364363173753389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66591059442242908782502259 99886589163364363173753389)
  ·
    refine ⟨37457470936261636190157521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99886589163364363173753389 37457470936261636190157521)
    ·
      refine ⟨28093103202196227142618141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37457470936261636190157521 28093103202196227142618141)
      ·
        refine ⟨10534913700823585178481803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28093103202196227142618141 10534913700823585178481803)
        ·
          refine ⟨15802370551235377767722705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10534913700823585178481803 15802370551235377767722705)
          ·
            refine ⟨11851777913426533325792029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15802370551235377767722705 11851777913426533325792029)
            ·
              refine ⟨4444416717534949997172011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11851777913426533325792029 4444416717534949997172011)
              ·
                refine ⟨6666625076302424995758017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4444416717534949997172011 6666625076302424995758017)
                ·
                  refine ⟨4999968807226818746818513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6666625076302424995758017 4999968807226818746818513)
                  ·
                    refine ⟨3749976605420114060113885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4999968807226818746818513 3749976605420114060113885)
                    ·
                      refine ⟨1406241227032542772542707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3749976605420114060113885 1406241227032542772542707)
                      ·
                        rfl

theorem cell23_2738645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2738645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738645 prefixEnd_2738645 := by exact prefixLift 2738645
  have htrace : WordTrace (prefixWord ++ tailWord_2738645) baseStart_2738645 baseEnd_2738645 := by
    simpa [prefixWord, tailWord_2738645, baseEnd_2738645] using wordTrace_append hprefix tailTrace_2738645
  have hstable : (prefixWord ++ tailWord_2738645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738645).length < 2 ^ (prefixWord ++ tailWord_2738645).sum := by decide
  have hdescent : baseEnd_2738645 < baseStart_2738645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738675 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 3]
def baseStart_2738675 : Nat := 118140960795 + 2738675 * 2 ^ 59
def prefixEnd_2738675 : Nat := 4983230072969 + 3 ^ 40 * 2738675 * 2
def baseEnd_2738675 : Nat := 1406256631452177655167569

theorem tailTrace_2738675 : CollatzResearch.WordTrace tailWord_2738675 prefixEnd_2738675 1406256631452177655167569 := by
  unfold tailWord_2738675
  simp only [CollatzResearch.WordTrace]
  refine ⟨99887683353255678297345479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66591788902170452198230319 99887683353255678297345479)
  ·
    refine ⟨149831525029883517446018219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99887683353255678297345479 149831525029883517446018219)
    ·
      refine ⟨224747287544825276169027329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149831525029883517446018219 224747287544825276169027329)
      ·
        refine ⟨168560465658618957126770497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224747287544825276169027329 168560465658618957126770497)
        ·
          refine ⟨126420349243964217845077873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168560465658618957126770497 126420349243964217845077873)
          ·
            refine ⟨94815261932973163383808405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126420349243964217845077873 94815261932973163383808405)
            ·
              refine ⟨4444465403108117033616019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94815261932973163383808405 4444465403108117033616019)
              ·
                refine ⟨6666698104662175550424029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4444465403108117033616019 6666698104662175550424029)
                ·
                  refine ⟨2500011789248315831409011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6666698104662175550424029 2500011789248315831409011)
                  ·
                    refine ⟨3750017683872473747113517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2500011789248315831409011 3750017683872473747113517)
                    ·
                      refine ⟨1406256631452177655167569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3750017683872473747113517 1406256631452177655167569)
                      ·
                        rfl

theorem cell23_2738675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 3].length) (baseStart_2738675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738675 prefixEnd_2738675 := by exact prefixLift 2738675
  have htrace : WordTrace (prefixWord ++ tailWord_2738675) baseStart_2738675 baseEnd_2738675 := by
    simpa [prefixWord, tailWord_2738675, baseEnd_2738675] using wordTrace_append hprefix tailTrace_2738675
  have hstable : (prefixWord ++ tailWord_2738675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738675).length < 2 ^ (prefixWord ++ tailWord_2738675).sum := by decide
  have hdescent : baseEnd_2738675 < baseStart_2738675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738692 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2738692 : Nat := 118140960795 + 2738692 * 2 ^ 59
def prefixEnd_2738692 : Nat := 4983230072969 + 3 ^ 40 * 2738692 * 2
def baseEnd_2738692 : Nat := 1406265360623304088654991

theorem tailTrace_2738692 : CollatzResearch.WordTrace tailWord_2738692 prefixEnd_2738692 1406265360623304088654991 := by
  unfold tailWord_2738692
  simp only [CollatzResearch.WordTrace]
  refine ⟨49944151697097045100357165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66592202262796060133809553 49944151697097045100357165)
  ·
    refine ⟨18729056886411391912633937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49944151697097045100357165 18729056886411391912633937)
    ·
      refine ⟨14046792664808543934475453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18729056886411391912633937 14046792664808543934475453)
      ·
        refine ⟨5267547249303203975428295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14046792664808543934475453 5267547249303203975428295)
        ·
          refine ⟨7901320873954805963142443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267547249303203975428295 7901320873954805963142443)
          ·
            refine ⟨11851981310932208944713665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7901320873954805963142443 11851981310932208944713665)
            ·
              refine ⟨8888985983199156708535249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11851981310932208944713665 8888985983199156708535249)
              ·
                refine ⟨6666739487399367531401437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8888985983199156708535249 6666739487399367531401437)
                ·
                  refine ⟨2500027307774762824275539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6666739487399367531401437 2500027307774762824275539)
                  ·
                    refine ⟨3750040961662144236413309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2500027307774762824275539 3750040961662144236413309)
                    ·
                      refine ⟨1406265360623304088654991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3750040961662144236413309 1406265360623304088654991)
                      ·
                        rfl

theorem cell23_2738692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2738692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738692 prefixEnd_2738692 := by exact prefixLift 2738692
  have htrace : WordTrace (prefixWord ++ tailWord_2738692) baseStart_2738692 baseEnd_2738692 := by
    simpa [prefixWord, tailWord_2738692, baseEnd_2738692] using wordTrace_append hprefix tailTrace_2738692
  have hstable : (prefixWord ++ tailWord_2738692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738692).length < 2 ^ (prefixWord ++ tailWord_2738692).sum := by decide
  have hdescent : baseEnd_2738692 < baseStart_2738692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738733 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 6]
def baseStart_2738733 : Nat := 118140960795 + 2738733 * 2 ^ 59
def prefixEnd_2738733 : Nat := 4983230072969 + 3 ^ 40 * 2738733 * 2
def baseEnd_2738733 : Nat := 156254045925570936471367

theorem tailTrace_2738733 : CollatzResearch.WordTrace tailWord_2738733 prefixEnd_2738733 156254045925570936471367 := by
  unfold tailWord_2738733
  simp only [CollatzResearch.WordTrace]
  refine ⟨99889798787045554202956853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66593199191363702801971235 99889798787045554202956853)
  ·
    refine ⟨9364668636285520706527205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99889798787045554202956853 9364668636285520706527205)
    ·
      refine ⟨1755875369303535132473851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9364668636285520706527205 1755875369303535132473851)
      ·
        refine ⟨2633813053955302698710777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1755875369303535132473851 2633813053955302698710777)
        ·
          refine ⟨1975359790466477024033083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2633813053955302698710777 1975359790466477024033083)
          ·
            refine ⟨2963039685699715536049625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975359790466477024033083 2963039685699715536049625)
            ·
              refine ⟨2222279764274786652037219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963039685699715536049625 2222279764274786652037219)
              ·
                refine ⟨3333419646412179978055829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222279764274786652037219 3333419646412179978055829)
                ·
                  refine ⟨156254045925570936471367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3333419646412179978055829 156254045925570936471367)
                  ·
                    rfl

theorem cell23_2738733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_2738733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738733 prefixEnd_2738733 := by exact prefixLift 2738733
  have htrace : WordTrace (prefixWord ++ tailWord_2738733) baseStart_2738733 baseEnd_2738733 := by
    simpa [prefixWord, tailWord_2738733, baseEnd_2738733] using wordTrace_append hprefix tailTrace_2738733
  have hstable : (prefixWord ++ tailWord_2738733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738733).length < 2 ^ (prefixWord ++ tailWord_2738733).sum := by decide
  have hdescent : baseEnd_2738733 < baseStart_2738733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738788 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_2738788 : Nat := 118140960795 + 2738788 * 2 ^ 59
def prefixEnd_2738788 : Nat := 4983230072969 + 3 ^ 40 * 2738788 * 2
def baseEnd_2738788 : Nat := 1406314654766135713054549

theorem tailTrace_2738788 : CollatzResearch.WordTrace tailWord_2738788 prefixEnd_2738788 1406314654766135713054549 := by
  unfold tailWord_2738788
  simp only [CollatzResearch.WordTrace]
  refine ⟨49945902400923149298104509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66594536534564199064139345 49945902400923149298104509)
  ·
    refine ⟨18729713400346180986789191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49945902400923149298104509 18729713400346180986789191)
    ·
      refine ⟨28094570100519271480183787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18729713400346180986789191 28094570100519271480183787)
      ·
        refine ⟨42141855150778907220275681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28094570100519271480183787 42141855150778907220275681)
        ·
          refine ⟨31606391363084180415206761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42141855150778907220275681 31606391363084180415206761)
          ·
            refine ⟨23704793522313135311405071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31606391363084180415206761 23704793522313135311405071)
            ·
              refine ⟨35557190283469702967107607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23704793522313135311405071 35557190283469702967107607)
              ·
                refine ⟨53335785425204554450661411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35557190283469702967107607 53335785425204554450661411)
                ·
                  refine ⟨80003678137806831675992117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53335785425204554450661411 80003678137806831675992117)
                  ·
                    refine ⟨7500344825419390469624261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80003678137806831675992117 7500344825419390469624261)
                    ·
                      refine ⟨1406314654766135713054549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7500344825419390469624261 1406314654766135713054549)
                      ·
                        rfl

theorem cell23_2738788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_2738788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738788 prefixEnd_2738788 := by exact prefixLift 2738788
  have htrace : WordTrace (prefixWord ++ tailWord_2738788) baseStart_2738788 baseEnd_2738788 := by
    simpa [prefixWord, tailWord_2738788, baseEnd_2738788] using wordTrace_append hprefix tailTrace_2738788
  have hstable : (prefixWord ++ tailWord_2738788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738788).length < 2 ^ (prefixWord ++ tailWord_2738788).sum := by decide
  have hdescent : baseEnd_2738788 < baseStart_2738788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738862 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_2738862 : Nat := 118140960795 + 2738862 * 2 ^ 59
def prefixEnd_2738862 : Nat := 4983230072969 + 3 ^ 40 * 2738862 * 2
def baseEnd_2738862 : Nat := 156261405814952047058801

theorem tailTrace_2738862 : CollatzResearch.WordTrace tailWord_2738862 prefixEnd_2738862 156261405814952047058801 := by
  unfold tailWord_2738862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12486812975447276154300355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66596335869052139489601893 12486812975447276154300355)
  ·
    refine ⟨18730219463170914231450533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12486812975447276154300355 18730219463170914231450533)
    ·
      refine ⟨3511916149344546418396975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18730219463170914231450533 3511916149344546418396975)
      ·
        refine ⟨5267874224016819627595463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3511916149344546418396975 5267874224016819627595463)
        ·
          refine ⟨7901811336025229441393195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267874224016819627595463 7901811336025229441393195)
          ·
            refine ⟨11852717004037844162089793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7901811336025229441393195 11852717004037844162089793)
            ·
              refine ⟨8889537753028383121567345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11852717004037844162089793 8889537753028383121567345)
              ·
                refine ⟨6667153314771287341175509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8889537753028383121567345 6667153314771287341175509)
                ·
                  refine ⟨156261405814952047058801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6667153314771287341175509 156261405814952047058801)
                  ·
                    rfl

theorem cell23_2738862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_2738862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738862 prefixEnd_2738862 := by exact prefixLift 2738862
  have htrace : WordTrace (prefixWord ++ tailWord_2738862) baseStart_2738862 baseEnd_2738862 := by
    simpa [prefixWord, tailWord_2738862, baseEnd_2738862] using wordTrace_append hprefix tailTrace_2738862
  have hstable : (prefixWord ++ tailWord_2738862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738862).length < 2 ^ (prefixWord ++ tailWord_2738862).sum := by decide
  have hdescent : baseEnd_2738862 < baseStart_2738862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738892 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_2738892 : Nat := 118140960795 + 2738892 * 2 ^ 59
def prefixEnd_2738892 : Nat := 4983230072969 + 3 ^ 40 * 2738892 * 2
def baseEnd_2738892 : Nat := 468789352251401102051357

theorem tailTrace_2738892 : CollatzResearch.WordTrace tailWord_2738892 prefixEnd_2738892 468789352251401102051357 := by
  unfold tailWord_2738892
  simp only [CollatzResearch.WordTrace]
  refine ⟨49947798996734762178997465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66597065328979682905329953 49947798996734762178997465)
  ·
    refine ⟨37460849247551071634248099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49947798996734762178997465 37460849247551071634248099)
    ·
      refine ⟨56191273871326607451372149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37460849247551071634248099 56191273871326607451372149)
      ·
        refine ⟨5267931925436869448566139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56191273871326607451372149 5267931925436869448566139)
        ·
          refine ⟨7901897888155304172849209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267931925436869448566139 7901897888155304172849209)
          ·
            refine ⟨5926423416116478129636907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7901897888155304172849209 5926423416116478129636907)
            ·
              refine ⟨8889635124174717194455361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5926423416116478129636907 8889635124174717194455361)
              ·
                refine ⟨6667226343131037895841521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8889635124174717194455361 6667226343131037895841521)
                ·
                  refine ⟨5000419757348278421881141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6667226343131037895841521 5000419757348278421881141)
                  ·
                    refine ⟨468789352251401102051357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5000419757348278421881141 468789352251401102051357)
                    ·
                      rfl

theorem cell23_2738892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_2738892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738892 prefixEnd_2738892 := by exact prefixLift 2738892
  have htrace : WordTrace (prefixWord ++ tailWord_2738892) baseStart_2738892 baseEnd_2738892 := by
    simpa [prefixWord, tailWord_2738892, baseEnd_2738892] using wordTrace_append hprefix tailTrace_2738892
  have hstable : (prefixWord ++ tailWord_2738892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738892).length < 2 ^ (prefixWord ++ tailWord_2738892).sum := by decide
  have hdescent : baseEnd_2738892 < baseStart_2738892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738952 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 6]
def baseStart_2738952 : Nat := 118140960795 + 2738952 * 2 ^ 59
def prefixEnd_2738952 : Nat := 4983230072969 + 3 ^ 40 * 2738952 * 2
def baseEnd_2738952 : Nat := 156266540621497007933755

theorem tailTrace_2738952 : CollatzResearch.WordTrace tailWord_2738952 prefixEnd_2738952 156266540621497007933755 := by
  unfold tailWord_2738952
  simp only [CollatzResearch.WordTrace]
  refine ⟨49948893186626077302589555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66598524248834769736786073 49948893186626077302589555)
  ·
    refine ⟨74923339779939115953884333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49948893186626077302589555 74923339779939115953884333)
    ·
      refine ⟨28096252417477168482706625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74923339779939115953884333 28096252417477168482706625)
      ·
        refine ⟨21072189313107876362029969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28096252417477168482706625 21072189313107876362029969)
        ·
          refine ⟨15804141984830907271522477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21072189313107876362029969 15804141984830907271522477)
          ·
            refine ⟨5926553244311590226820929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15804141984830907271522477 5926553244311590226820929)
            ·
              refine ⟨4444914933233692670115697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5926553244311590226820929 4444914933233692670115697)
              ·
                refine ⟨3333686199925269502586773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4444914933233692670115697 3333686199925269502586773)
                ·
                  refine ⟨156266540621497007933755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3333686199925269502586773 156266540621497007933755)
                  ·
                    rfl

theorem cell23_2738952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 6].length) (baseStart_2738952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738952 prefixEnd_2738952 := by exact prefixLift 2738952
  have htrace : WordTrace (prefixWord ++ tailWord_2738952) baseStart_2738952 baseEnd_2738952 := by
    simpa [prefixWord, tailWord_2738952, baseEnd_2738952] using wordTrace_append hprefix tailTrace_2738952
  have hstable : (prefixWord ++ tailWord_2738952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738952).length < 2 ^ (prefixWord ++ tailWord_2738952).sum := by decide
  have hdescent : baseEnd_2738952 < baseStart_2738952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2738965 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_2738965 : Nat := 118140960795 + 2738965 * 2 ^ 59
def prefixEnd_2738965 : Nat := 4983230072969 + 3 ^ 40 * 2738965 * 2
def baseEnd_2738965 : Nat := 468801846947327173513745

theorem tailTrace_2738965 : CollatzResearch.WordTrace tailWord_2738965 prefixEnd_2738965 468801846947327173513745 := by
  unfold tailWord_2738965
  simp only [CollatzResearch.WordTrace]
  refine ⟨99898260522205057825402349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66598840348136705216934899 99898260522205057825402349)
  ·
    refine ⟨37461847695826896684525881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99898260522205057825402349 37461847695826896684525881)
    ·
      refine ⟨28096385771870172513394411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37461847695826896684525881 28096385771870172513394411)
      ·
        refine ⟨42144578657805258770091617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28096385771870172513394411 42144578657805258770091617)
        ·
          refine ⟨31608433993353944077568713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42144578657805258770091617 31608433993353944077568713)
          ·
            refine ⟨23706325495015458058176535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31608433993353944077568713 23706325495015458058176535)
            ·
              refine ⟨35559488242523187087264803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23706325495015458058176535 35559488242523187087264803)
              ·
                refine ⟨53339232363784780630897205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35559488242523187087264803 53339232363784780630897205)
                ·
                  refine ⟨5000553034104823184146613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53339232363784780630897205 5000553034104823184146613)
                  ·
                    refine ⟨468801846947327173513745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5000553034104823184146613 468801846947327173513745)
                    ·
                      rfl

theorem cell23_2738965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_2738965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2738965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2738965 prefixEnd_2738965 := by exact prefixLift 2738965
  have htrace : WordTrace (prefixWord ++ tailWord_2738965) baseStart_2738965 baseEnd_2738965 := by
    simpa [prefixWord, tailWord_2738965, baseEnd_2738965] using wordTrace_append hprefix tailTrace_2738965
  have hstable : (prefixWord ++ tailWord_2738965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2738965).length < 2 ^ (prefixWord ++ tailWord_2738965).sum := by decide
  have hdescent : baseEnd_2738965 < baseStart_2738965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2738965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739015 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_2739015 : Nat := 118140960795 + 2739015 * 2 ^ 59
def prefixEnd_2739015 : Nat := 4983230072969 + 3 ^ 40 * 2739015 * 2
def baseEnd_2739015 : Nat := 1406431214874706324916005

theorem tailTrace_2739015 : CollatzResearch.WordTrace tailWord_2739015 prefixEnd_2739015 1406431214874706324916005 := by
  unfold tailWord_2739015
  simp only [CollatzResearch.WordTrace]
  refine ⟨99900084172023916364722499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66600056114682610909814999 99900084172023916364722499)
  ·
    refine ⟨149850126258035874547083749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99900084172023916364722499 149850126258035874547083749)
    ·
      refine ⟨28096898673381726477578203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149850126258035874547083749 28096898673381726477578203)
      ·
        refine ⟨42145348010072589716367305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28096898673381726477578203 42145348010072589716367305)
        ·
          refine ⟨31609011007554442287275479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42145348010072589716367305 31609011007554442287275479)
          ·
            refine ⟨47413516511331663430913219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31609011007554442287275479 47413516511331663430913219)
            ·
              refine ⟨71120274766997495146369829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47413516511331663430913219 71120274766997495146369829)
              ·
                refine ⟨13335051518812030339944343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71120274766997495146369829 13335051518812030339944343)
                ·
                  refine ⟨20002577278218045509916515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13335051518812030339944343 20002577278218045509916515)
                  ·
                    refine ⟨30003865917327068264874773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20002577278218045509916515 30003865917327068264874773)
                    ·
                      refine ⟨1406431214874706324916005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30003865917327068264874773 1406431214874706324916005)
                      ·
                        rfl

theorem cell23_2739015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_2739015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739015 prefixEnd_2739015 := by exact prefixLift 2739015
  have htrace : WordTrace (prefixWord ++ tailWord_2739015) baseStart_2739015 baseEnd_2739015 := by
    simpa [prefixWord, tailWord_2739015, baseEnd_2739015] using wordTrace_append hprefix tailTrace_2739015
  have hstable : (prefixWord ++ tailWord_2739015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739015).length < 2 ^ (prefixWord ++ tailWord_2739015).sum := by decide
  have hdescent : baseEnd_2739015 < baseStart_2739015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739022 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_2739022 : Nat := 118140960795 + 2739022 * 2 ^ 59
def prefixEnd_2739022 : Nat := 4983230072969 + 3 ^ 40 * 2739022 * 2
def baseEnd_2739022 : Nat := 1406434809239287797528473

theorem tailTrace_2739022 : CollatzResearch.WordTrace tailWord_2739022 prefixEnd_2739022 1406434809239287797528473 := by
  unfold tailWord_2739022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12487542435374819570028415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66600226321999037706818213 12487542435374819570028415)
  ·
    refine ⟨18731313653062229355042623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12487542435374819570028415 18731313653062229355042623)
    ·
      refine ⟨28096970479593344032563935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18731313653062229355042623 28096970479593344032563935)
      ·
        refine ⟨42145455719390016048845903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28096970479593344032563935 42145455719390016048845903)
        ·
          refine ⟨63218183579085024073268855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42145455719390016048845903 63218183579085024073268855)
          ·
            refine ⟨94827275368627536109903283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63218183579085024073268855 94827275368627536109903283)
            ·
              refine ⟨142240913052941304164854925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94827275368627536109903283 142240913052941304164854925)
              ·
                refine ⟨53340342394852989061820597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142240913052941304164854925 53340342394852989061820597)
                ·
                  refine ⟨5000657099517467724545681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53340342394852989061820597 5000657099517467724545681)
                  ·
                    refine ⟨3750492824638100793409261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5000657099517467724545681 3750492824638100793409261)
                    ·
                      refine ⟨1406434809239287797528473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3750492824638100793409261 1406434809239287797528473)
                      ·
                        rfl

theorem cell23_2739022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_2739022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2739022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2739022 prefixEnd_2739022 := by exact prefixLift 2739022
  have htrace : WordTrace (prefixWord ++ tailWord_2739022) baseStart_2739022 baseEnd_2739022 := by
    simpa [prefixWord, tailWord_2739022, baseEnd_2739022] using wordTrace_append hprefix tailTrace_2739022
  have hstable : (prefixWord ++ tailWord_2739022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739022).length < 2 ^ (prefixWord ++ tailWord_2739022).sum := by decide
  have hdescent : baseEnd_2739022 < baseStart_2739022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
