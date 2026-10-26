import V185TrunkScan23Chunk0520

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3080536 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 2, 2, 2]
def baseStart_3080536 : Nat := 118140960795 + 3080536 * 2 ^ 59
def prefixEnd_3080536 : Nat := 4983230072969 + 3 ^ 40 * 3080536 * 2
def baseEnd_3080536 : Nat := 1581795641478864622432879

theorem tailTrace_3080536 : CollatzResearch.WordTrace tailWord_3080536 prefixEnd_3080536 1581795641478864622432879 := by
  unfold tailWord_3080536
  simp only [CollatzResearch.WordTrace]
  refine ⟨56178189183875830253930731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74904252245167773671907641 56178189183875830253930731)
  ·
    refine ⟨84267283775813745380896097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56178189183875830253930731 84267283775813745380896097)
    ·
      refine ⟨63200462831860309035672073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84267283775813745380896097 63200462831860309035672073)
      ·
        refine ⟨47400347123895231776754055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63200462831860309035672073 47400347123895231776754055)
        ·
          refine ⟨71100520685842847665131083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47400347123895231776754055 71100520685842847665131083)
          ·
            refine ⟨106650781028764271497696625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71100520685842847665131083 106650781028764271497696625)
            ·
              refine ⟨79988085771573203623272469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106650781028764271497696625 79988085771573203623272469)
              ·
                refine ⟨3749441520542493919840897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79988085771573203623272469 3749441520542493919840897)
                ·
                  refine ⟨2812081140406870439880673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3749441520542493919840897 2812081140406870439880673)
                  ·
                    refine ⟨2109060855305152829910505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2812081140406870439880673 2109060855305152829910505)
                    ·
                      refine ⟨1581795641478864622432879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109060855305152829910505 1581795641478864622432879)
                      ·
                        rfl

theorem cell23_3080536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_3080536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080536 prefixEnd_3080536 := by exact prefixLift 3080536
  have htrace : WordTrace (prefixWord ++ tailWord_3080536) baseStart_3080536 baseEnd_3080536 := by
    simpa [prefixWord, tailWord_3080536, baseEnd_3080536] using wordTrace_append hprefix tailTrace_3080536
  have hstable : (prefixWord ++ tailWord_3080536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080536).length < 2 ^ (prefixWord ++ tailWord_3080536).sum := by decide
  have hdescent : baseEnd_3080536 < baseStart_3080536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080553 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 2, 2, 2]
def baseStart_3080553 : Nat := 118140960795 + 3080553 * 2 ^ 59
def prefixEnd_3080553 : Nat := 4983230072969 + 3 ^ 40 * 3080553 * 2
def baseEnd_3080553 : Nat := 1581804370649991055920301

theorem tailTrace_3080553 : CollatzResearch.WordTrace tailWord_3080553 prefixEnd_3080553 1581804370649991055920301 := by
  unfold tailWord_3080553
  simp only [CollatzResearch.WordTrace]
  refine ⟨112356998408690072411230313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74904665605793381607486875 112356998408690072411230313)
  ·
    refine ⟨84267748806517554308422735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112356998408690072411230313 84267748806517554308422735)
    ·
      refine ⟨126401623209776331462634103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84267748806517554308422735 126401623209776331462634103)
      ·
        refine ⟨189602434814664497193951155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126401623209776331462634103 189602434814664497193951155)
        ·
          refine ⟨284403652221996745790926733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189602434814664497193951155 284403652221996745790926733)
          ·
            refine ⟨106651369583248779671597525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284403652221996745790926733 106651369583248779671597525)
            ·
              refine ⟨2499641474607393273553067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 106651369583248779671597525 2499641474607393273553067)
              ·
                refine ⟨3749462211911089910329601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499641474607393273553067 3749462211911089910329601)
                ·
                  refine ⟨2812096658933317432747201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3749462211911089910329601 2812096658933317432747201)
                  ·
                    refine ⟨2109072494199988074560401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2812096658933317432747201 2109072494199988074560401)
                    ·
                      refine ⟨1581804370649991055920301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109072494199988074560401 1581804370649991055920301)
                      ·
                        rfl

theorem cell23_3080553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 2, 2].length) (baseStart_3080553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080553 prefixEnd_3080553 := by exact prefixLift 3080553
  have htrace : WordTrace (prefixWord ++ tailWord_3080553) baseStart_3080553 baseEnd_3080553 := by
    simpa [prefixWord, tailWord_3080553, baseEnd_3080553] using wordTrace_append hprefix tailTrace_3080553
  have hstable : (prefixWord ++ tailWord_3080553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080553).length < 2 ^ (prefixWord ++ tailWord_3080553).sum := by decide
  have hdescent : baseEnd_3080553 < baseStart_3080553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080672 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3080672 : Nat := 118140960795 + 3080672 * 2 ^ 59
def prefixEnd_3080672 : Nat := 4983230072969 + 3 ^ 40 * 3080672 * 2
def baseEnd_3080672 : Nat := 1581865474847876090332253

theorem tailTrace_3080672 : CollatzResearch.WordTrace tailWord_3080672 prefixEnd_3080672 1581865474847876090332253 := by
  unfold tailWord_3080672
  simp only [CollatzResearch.WordTrace]
  refine ⟨56180669347629477867406135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74907559130172637156541513 56180669347629477867406135)
  ·
    refine ⟨84271004021444216801109203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56180669347629477867406135 84271004021444216801109203)
    ·
      refine ⟨126406506032166325201663805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84271004021444216801109203 126406506032166325201663805)
      ·
        refine ⟨47402439762062371950623927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126406506032166325201663805 47402439762062371950623927)
        ·
          refine ⟨71103659643093557925935891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47402439762062371950623927 71103659643093557925935891)
          ·
            refine ⟨106655489464640336888903837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71103659643093557925935891 106655489464640336888903837)
            ·
              refine ⟨39995808549240126333338939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106655489464640336888903837 39995808549240126333338939)
              ·
                refine ⟨59993712823860189500008409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39995808549240126333338939 59993712823860189500008409)
                ·
                  refine ⟨44995284617895142125006307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59993712823860189500008409 44995284617895142125006307)
                  ·
                    refine ⟨67492926926842713187509461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44995284617895142125006307 67492926926842713187509461)
                    ·
                      refine ⟨1581865474847876090332253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67492926926842713187509461 1581865474847876090332253)
                      ·
                        rfl

theorem cell23_3080672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3080672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080672 prefixEnd_3080672 := by exact prefixLift 3080672
  have htrace : WordTrace (prefixWord ++ tailWord_3080672) baseStart_3080672 baseEnd_3080672 := by
    simpa [prefixWord, tailWord_3080672, baseEnd_3080672] using wordTrace_append hprefix tailTrace_3080672
  have hstable : (prefixWord ++ tailWord_3080672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080672).length < 2 ^ (prefixWord ++ tailWord_3080672).sum := by decide
  have hdescent : baseEnd_3080672 < baseStart_3080672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080679 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3080679 : Nat := 118140960795 + 3080679 * 2 ^ 59
def prefixEnd_3080679 : Nat := 4983230072969 + 3 ^ 40 * 3080679 * 2
def baseEnd_3080679 : Nat := 527289689737485854314907

theorem tailTrace_3080679 : CollatzResearch.WordTrace tailWord_3080679 prefixEnd_3080679 527289689737485854314907 := by
  unfold tailWord_3080679
  simp only [CollatzResearch.WordTrace]
  refine ⟨112361594006233595930317091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74907729337489063953544727 112361594006233595930317091)
  ·
    refine ⟨168542391009350393895475637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112361594006233595930317091 168542391009350393895475637)
    ·
      refine ⟨15800849157126599427700841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168542391009350393895475637 15800849157126599427700841)
      ·
        refine ⟨11850636867844949570775631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15800849157126599427700841 11850636867844949570775631)
        ·
          refine ⟨17775955301767424356163447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11850636867844949570775631 17775955301767424356163447)
          ·
            refine ⟨26663932952651136534245171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17775955301767424356163447 26663932952651136534245171)
            ·
              refine ⟨39995899428976704801367757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26663932952651136534245171 39995899428976704801367757)
              ·
                refine ⟨14998462285866264300512909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39995899428976704801367757 14998462285866264300512909)
                ·
                  refine ⟨5624423357199849112692341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14998462285866264300512909 5624423357199849112692341)
                  ·
                    refine ⟨527289689737485854314907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5624423357199849112692341 527289689737485854314907)
                    ·
                      rfl

theorem cell23_3080679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3080679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080679 prefixEnd_3080679 := by exact prefixLift 3080679
  have htrace : WordTrace (prefixWord ++ tailWord_3080679) baseStart_3080679 baseEnd_3080679 := by
    simpa [prefixWord, tailWord_3080679, baseEnd_3080679] using wordTrace_append hprefix tailTrace_3080679
  have hstable : (prefixWord ++ tailWord_3080679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080679).length < 2 ^ (prefixWord ++ tailWord_3080679).sum := by decide
  have hdescent : baseEnd_3080679 < baseStart_3080679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080733 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_3080733 : Nat := 118140960795 + 3080733 * 2 ^ 59
def prefixEnd_3080733 : Nat := 4983230072969 + 3 ^ 40 * 3080733 * 2
def baseEnd_3080733 : Nat := 1581896797167800351669473

theorem tailTrace_3080733 : CollatzResearch.WordTrace tailWord_3080733 prefixEnd_3080733 1581896797167800351669473 := by
  unfold tailWord_3080733
  simp only [CollatzResearch.WordTrace]
  refine ⟨112363563548037963152782853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74909042365358642101855235 112363563548037963152782853)
  ·
    refine ⟨21068168165257118091146785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112363563548037963152782853 21068168165257118091146785)
    ·
      refine ⟨15801126123942838568360089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21068168165257118091146785 15801126123942838568360089)
      ·
        refine ⟨11850844592957128926270067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15801126123942838568360089 11850844592957128926270067)
        ·
          refine ⟨17776266889435693389405101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11850844592957128926270067 17776266889435693389405101)
          ·
            refine ⟨6666100083538385021026913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17776266889435693389405101 6666100083538385021026913)
            ·
              refine ⟨4999575062653788765770185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6666100083538385021026913 4999575062653788765770185)
              ·
                refine ⟨3749681296990341574327639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4999575062653788765770185 3749681296990341574327639)
                ·
                  refine ⟨5624521945485512361491459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3749681296990341574327639 5624521945485512361491459)
                  ·
                    refine ⟨8436782918228268542237189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5624521945485512361491459 8436782918228268542237189)
                    ·
                      refine ⟨1581896797167800351669473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8436782918228268542237189 1581896797167800351669473)
                      ·
                        rfl

theorem cell23_3080733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_3080733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080733 prefixEnd_3080733 := by exact prefixLift 3080733
  have htrace : WordTrace (prefixWord ++ tailWord_3080733) baseStart_3080733 baseEnd_3080733 := by
    simpa [prefixWord, tailWord_3080733, baseEnd_3080733] using wordTrace_append hprefix tailTrace_3080733
  have hstable : (prefixWord ++ tailWord_3080733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080733).length < 2 ^ (prefixWord ++ tailWord_3080733).sum := by decide
  have hdescent : baseEnd_3080733 < baseStart_3080733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080739 : List Nat := [1, 1, 1, 4, 4, 2, 1, 9]
def baseStart_3080739 : Nat := 118140960795 + 3080739 * 2 ^ 59
def prefixEnd_3080739 : Nat := 4983230072969 + 3 ^ 40 * 3080739 * 2
def baseEnd_3080739 : Nat := 58588884372286197340535

theorem tailTrace_3080739 : CollatzResearch.WordTrace tailWord_3080739 prefixEnd_3080739 58588884372286197340535 := by
  unfold tailWord_3080739
  simp only [CollatzResearch.WordTrace]
  refine ⟨112363782386016226177501271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74909188257344150785000847 112363782386016226177501271)
  ·
    refine ⟨168545673579024339266251907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112363782386016226177501271 168545673579024339266251907)
    ·
      refine ⟨252818510368536508899377861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168545673579024339266251907 252818510368536508899377861)
      ·
        refine ⟨47403470694100595418633349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252818510368536508899377861 47403470694100595418633349)
        ·
          refine ⟨8888150755143861640993753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47403470694100595418633349 8888150755143861640993753)
          ·
            refine ⟨6666113066357896230745315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8888150755143861640993753 6666113066357896230745315)
            ·
              refine ⟨9999169599536844346117973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6666113066357896230745315 9999169599536844346117973)
              ·
                refine ⟨58588884372286197340535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9999169599536844346117973 58588884372286197340535)
                ·
                  rfl

theorem cell23_3080739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 9].length) (baseStart_3080739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080739 prefixEnd_3080739 := by exact prefixLift 3080739
  have htrace : WordTrace (prefixWord ++ tailWord_3080739) baseStart_3080739 baseEnd_3080739 := by
    simpa [prefixWord, tailWord_3080739, baseEnd_3080739] using wordTrace_append hprefix tailTrace_3080739
  have hstable : (prefixWord ++ tailWord_3080739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080739).length < 2 ^ (prefixWord ++ tailWord_3080739).sum := by decide
  have hdescent : baseEnd_3080739 < baseStart_3080739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080767 : List Nat := [1, 1, 2, 2, 3, 2, 5, 2, 1, 2, 2]
def baseStart_3080767 : Nat := 118140960795 + 3080767 * 2 ^ 59
def prefixEnd_3080767 : Nat := 4983230072969 + 3 ^ 40 * 3080767 * 2
def baseEnd_3080767 : Nat := 1581914255510053218644317

theorem tailTrace_3080767 : CollatzResearch.WordTrace tailWord_3080767 prefixEnd_3080767 1581914255510053218644317 := by
  unfold tailWord_3080767
  simp only [CollatzResearch.WordTrace]
  refine ⟨112364803629914786959520555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74909869086609857973013703 112364803629914786959520555)
  ·
    refine ⟨168547205444872180439280833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112364803629914786959520555 168547205444872180439280833)
    ·
      refine ⟨126410404083654135329460625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168547205444872180439280833 126410404083654135329460625)
      ·
        refine ⟨94807803062740601497095469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126410404083654135329460625 94807803062740601497095469)
        ·
          refine ⟨35552926148527725561410801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94807803062740601497095469 35552926148527725561410801)
          ·
            refine ⟨26664694611395794171058101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35552926148527725561410801 26664694611395794171058101)
            ·
              refine ⟨2499815119818355703536697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26664694611395794171058101 2499815119818355703536697)
              ·
                refine ⟨1874861339863766777652523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499815119818355703536697 1874861339863766777652523)
                ·
                  refine ⟨2812292009795650166478785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874861339863766777652523 2812292009795650166478785)
                  ·
                    refine ⟨2109219007346737624859089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2812292009795650166478785 2109219007346737624859089)
                    ·
                      refine ⟨1581914255510053218644317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109219007346737624859089 1581914255510053218644317)
                      ·
                        rfl

theorem cell23_3080767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 2, 2].length) (baseStart_3080767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080767 prefixEnd_3080767 := by exact prefixLift 3080767
  have htrace : WordTrace (prefixWord ++ tailWord_3080767) baseStart_3080767 baseEnd_3080767 := by
    simpa [prefixWord, tailWord_3080767, baseEnd_3080767] using wordTrace_append hprefix tailTrace_3080767
  have hstable : (prefixWord ++ tailWord_3080767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080767).length < 2 ^ (prefixWord ++ tailWord_3080767).sum := by decide
  have hdescent : baseEnd_3080767 < baseStart_3080767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080823 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 4, 2, 2]
def baseStart_3080823 : Nat := 118140960795 + 3080823 * 2 ^ 59
def prefixEnd_3080823 : Nat := 4983230072969 + 3 ^ 40 * 3080823 * 2
def baseEnd_3080823 : Nat := 1581943010426704999544059

theorem tailTrace_3080823 : CollatzResearch.WordTrace tailWord_3080823 prefixEnd_3080823 1581943010426704999544059 := by
  unfold tailWord_3080823
  simp only [CollatzResearch.WordTrace]
  refine ⟨112366846117711908523559123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74911230745141272349039415 112366846117711908523559123)
  ·
    refine ⟨168550269176567862785338685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112366846117711908523559123 168550269176567862785338685)
    ·
      refine ⟨63206350941212948544502007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168550269176567862785338685 63206350941212948544502007)
      ·
        refine ⟨94809526411819422816753011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63206350941212948544502007 94809526411819422816753011)
        ·
          refine ⟨142214289617729134225129517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94809526411819422816753011 142214289617729134225129517)
          ·
            refine ⟨53330358606648425334423569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142214289617729134225129517 53330358606648425334423569)
            ·
              refine ⟨39997768954986319000817677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53330358606648425334423569 39997768954986319000817677)
              ·
                refine ⟨14999163358119869625306629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39997768954986319000817677 14999163358119869625306629)
                ·
                  refine ⟨2812343129647475554744993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14999163358119869625306629 2812343129647475554744993)
                  ·
                    refine ⟨2109257347235606666058745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2812343129647475554744993 2109257347235606666058745)
                    ·
                      refine ⟨1581943010426704999544059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109257347235606666058745 1581943010426704999544059)
                      ·
                        rfl

theorem cell23_3080823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_3080823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080823 prefixEnd_3080823 := by exact prefixLift 3080823
  have htrace : WordTrace (prefixWord ++ tailWord_3080823) baseStart_3080823 baseEnd_3080823 := by
    simpa [prefixWord, tailWord_3080823, baseEnd_3080823] using wordTrace_append hprefix tailTrace_3080823
  have hstable : (prefixWord ++ tailWord_3080823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080823).length < 2 ^ (prefixWord ++ tailWord_3080823).sum := by decide
  have hdescent : baseEnd_3080823 < baseStart_3080823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080834 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3080834 : Nat := 118140960795 + 3080834 * 2 ^ 59
def prefixEnd_3080834 : Nat := 4983230072969 + 3 ^ 40 * 3080834 * 2
def baseEnd_3080834 : Nat := 1581948658713904456506509

theorem tailTrace_3080834 : CollatzResearch.WordTrace tailWord_3080834 prefixEnd_3080834 1581948658713904456506509 := by
  unfold tailWord_3080834
  simp only [CollatzResearch.WordTrace]
  refine ⟨28091811830168014350552389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74911498213781371601473037 28091811830168014350552389)
  ·
    refine ⟨5267214718156502690728573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28091811830168014350552389 5267214718156502690728573)
    ·
      refine ⟨1975205519308688509023215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5267214718156502690728573 1975205519308688509023215)
      ·
        refine ⟨2962808278963032763534823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975205519308688509023215 2962808278963032763534823)
        ·
          refine ⟨4444212418444549145302235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962808278963032763534823 4444212418444549145302235)
          ·
            refine ⟨6666318627666823717953353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444212418444549145302235 6666318627666823717953353)
            ·
              refine ⟨4999738970750117788465015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6666318627666823717953353 4999738970750117788465015)
              ·
                refine ⟨7499608456125176682697523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4999738970750117788465015 7499608456125176682697523)
                ·
                  refine ⟨11249412684187765024046285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7499608456125176682697523 11249412684187765024046285)
                  ·
                    refine ⟨4218529756570411884017357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11249412684187765024046285 4218529756570411884017357)
                    ·
                      refine ⟨1581948658713904456506509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4218529756570411884017357 1581948658713904456506509)
                      ·
                        rfl

theorem cell23_3080834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3080834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080834 prefixEnd_3080834 := by exact prefixLift 3080834
  have htrace : WordTrace (prefixWord ++ tailWord_3080834) baseStart_3080834 baseEnd_3080834 := by
    simpa [prefixWord, tailWord_3080834, baseEnd_3080834] using wordTrace_append hprefix tailTrace_3080834
  have hstable : (prefixWord ++ tailWord_3080834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080834).length < 2 ^ (prefixWord ++ tailWord_3080834).sum := by decide
  have hdescent : baseEnd_3080834 < baseStart_3080834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080836 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3080836 : Nat := 118140960795 + 3080836 * 2 ^ 59
def prefixEnd_3080836 : Nat := 4983230072969 + 3 ^ 40 * 3080836 * 2
def baseEnd_3080836 : Nat := 1581949685675213448681499

theorem tailTrace_3080836 : CollatzResearch.WordTrace tailWord_3080836 prefixEnd_3080836 1581949685675213448681499 := by
  unfold tailWord_3080836
  simp only [CollatzResearch.WordTrace]
  refine ⟨56183660133332405871891181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74911546844443207829188241 56183660133332405871891181)
  ·
    refine ⟨21068872549999652201959193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56183660133332405871891181 21068872549999652201959193)
    ·
      refine ⟨15801654412499739151469395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21068872549999652201959193 15801654412499739151469395)
      ·
        refine ⟨23702481618749608727204093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15801654412499739151469395 23702481618749608727204093)
        ·
          refine ⟨8888430607031103272701535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23702481618749608727204093 8888430607031103272701535)
          ·
            refine ⟨13332645910546654909052303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8888430607031103272701535 13332645910546654909052303)
            ·
              refine ⟨19998968865819982363578455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13332645910546654909052303 19998968865819982363578455)
              ·
                refine ⟨29998453298729973545367683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19998968865819982363578455 29998453298729973545367683)
                ·
                  refine ⟨44997679948094960318051525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29998453298729973545367683 44997679948094960318051525)
                  ·
                    refine ⟨8437064990267805059634661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44997679948094960318051525 8437064990267805059634661)
                    ·
                      refine ⟨1581949685675213448681499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8437064990267805059634661 1581949685675213448681499)
                      ·
                        rfl

theorem cell23_3080836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3080836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080836 prefixEnd_3080836 := by exact prefixLift 3080836
  have htrace : WordTrace (prefixWord ++ tailWord_3080836) baseStart_3080836 baseEnd_3080836 := by
    simpa [prefixWord, tailWord_3080836, baseEnd_3080836] using wordTrace_append hprefix tailTrace_3080836
  have hstable : (prefixWord ++ tailWord_3080836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080836).length < 2 ^ (prefixWord ++ tailWord_3080836).sum := by decide
  have hdescent : baseEnd_3080836 < baseStart_3080836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080846 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_3080846 : Nat := 118140960795 + 3080846 * 2 ^ 59
def prefixEnd_3080846 : Nat := 4983230072969 + 3 ^ 40 * 3080846 * 2
def baseEnd_3080846 : Nat := 175772757831306489950717

theorem tailTrace_3080846 : CollatzResearch.WordTrace tailWord_3080846 prefixEnd_3080846 175772757831306489950717 := by
  unfold tailWord_3080846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045960624578572931455799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74911789997752388967764261 14045960624578572931455799)
  ·
    refine ⟨21068940936867859397183699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14045960624578572931455799 21068940936867859397183699)
    ·
      refine ⟨31603411405301789095775549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21068940936867859397183699 31603411405301789095775549)
      ·
        refine ⟨11851279276988170910915831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31603411405301789095775549 11851279276988170910915831)
        ·
          refine ⟨17776918915482256366373747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11851279276988170910915831 17776918915482256366373747)
          ·
            refine ⟨26665378373223384549560621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17776918915482256366373747 26665378373223384549560621)
            ·
              refine ⟨9999516889958769206085233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26665378373223384549560621 9999516889958769206085233)
              ·
                refine ⟨7499637667469076904563925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9999516889958769206085233 7499637667469076904563925)
                ·
                  refine ⟨175772757831306489950717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7499637667469076904563925 175772757831306489950717)
                  ·
                    rfl

theorem cell23_3080846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_3080846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080846 prefixEnd_3080846 := by exact prefixLift 3080846
  have htrace : WordTrace (prefixWord ++ tailWord_3080846) baseStart_3080846 baseEnd_3080846 := by
    simpa [prefixWord, tailWord_3080846, baseEnd_3080846] using wordTrace_append hprefix tailTrace_3080846
  have hstable : (prefixWord ++ tailWord_3080846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080846).length < 2 ^ (prefixWord ++ tailWord_3080846).sum := by decide
  have hdescent : baseEnd_3080846 < baseStart_3080846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080856 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3080856 : Nat := 118140960795 + 3080856 * 2 ^ 59
def prefixEnd_3080856 : Nat := 4983230072969 + 3 ^ 40 * 3080856 * 2
def baseEnd_3080856 : Nat := 1581959955288303370431407

theorem tailTrace_3080856 : CollatzResearch.WordTrace tailWord_3080856 prefixEnd_3080856 1581959955288303370431407 := by
  unfold tailWord_3080856
  simp only [CollatzResearch.WordTrace]
  refine ⟨56184024863296177579755211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74912033151061570106340281 56184024863296177579755211)
  ·
    refine ⟨84276037294944266369632817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56184024863296177579755211 84276037294944266369632817)
    ·
      refine ⟨63207027971208199777224613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84276037294944266369632817 63207027971208199777224613)
      ·
        refine ⟨11851317744601537458229615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63207027971208199777224613 11851317744601537458229615)
        ·
          refine ⟨17776976616902306187344423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11851317744601537458229615 17776976616902306187344423)
          ·
            refine ⟨26665464925353459281016635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17776976616902306187344423 26665464925353459281016635)
            ·
              refine ⟨39998197388030188921524953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26665464925353459281016635 39998197388030188921524953)
              ·
                refine ⟨29998648041022641691143715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39998197388030188921524953 29998648041022641691143715)
                ·
                  refine ⟨44997972061533962536715573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29998648041022641691143715 44997972061533962536715573)
                  ·
                    refine ⟨4218559880768808987817085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44997972061533962536715573 4218559880768808987817085)
                    ·
                      refine ⟨1581959955288303370431407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4218559880768808987817085 1581959955288303370431407)
                      ·
                        rfl

theorem cell23_3080856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3080856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080856 prefixEnd_3080856 := by exact prefixLift 3080856
  have htrace : WordTrace (prefixWord ++ tailWord_3080856) baseStart_3080856 baseEnd_3080856 := by
    simpa [prefixWord, tailWord_3080856, baseEnd_3080856] using wordTrace_append hprefix tailTrace_3080856
  have hstable : (prefixWord ++ tailWord_3080856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080856).length < 2 ^ (prefixWord ++ tailWord_3080856).sum := by decide
  have hdescent : baseEnd_3080856 < baseStart_3080856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080874 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3080874 : Nat := 118140960795 + 3080874 * 2 ^ 59
def prefixEnd_3080874 : Nat := 4983230072969 + 3 ^ 40 * 3080874 * 2
def baseEnd_3080874 : Nat := 1581969197940084300006325

theorem tailTrace_3080874 : CollatzResearch.WordTrace tailWord_3080874 prefixEnd_3080874 1581969197940084300006325 := by
  unfold tailWord_3080874
  simp only [CollatzResearch.WordTrace]
  refine ⟨28092176560131786058416419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74912470827018096155777117 28092176560131786058416419)
  ·
    refine ⟨42138264840197679087624629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28092176560131786058416419 42138264840197679087624629)
    ·
      refine ⟨3950462328768532414464809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42138264840197679087624629 3950462328768532414464809)
      ·
        refine ⟨2962846746576399310848607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3950462328768532414464809 2962846746576399310848607)
        ·
          refine ⟨4444270119864598966272911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962846746576399310848607 4444270119864598966272911)
          ·
            refine ⟨6666405179796898449409367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444270119864598966272911 6666405179796898449409367)
            ·
              refine ⟨9999607769695347674114051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6666405179796898449409367 9999607769695347674114051)
              ·
                refine ⟨14999411654543021511171077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9999607769695347674114051 14999411654543021511171077)
                ·
                  refine ⟨2812389685226816533344577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14999411654543021511171077 2812389685226816533344577)
                  ·
                    refine ⟨2109292263920112400008433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2812389685226816533344577 2109292263920112400008433)
                    ·
                      refine ⟨1581969197940084300006325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109292263920112400008433 1581969197940084300006325)
                      ·
                        rfl

theorem cell23_3080874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3080874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080874 prefixEnd_3080874 := by exact prefixLift 3080874
  have htrace : WordTrace (prefixWord ++ tailWord_3080874) baseStart_3080874 baseEnd_3080874 := by
    simpa [prefixWord, tailWord_3080874, baseEnd_3080874] using wordTrace_append hprefix tailTrace_3080874
  have hstable : (prefixWord ++ tailWord_3080874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080874).length < 2 ^ (prefixWord ++ tailWord_3080874).sum := by decide
  have hdescent : baseEnd_3080874 < baseStart_3080874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080896 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_3080896 : Nat := 118140960795 + 3080896 * 2 ^ 59
def prefixEnd_3080896 : Nat := 4983230072969 + 3 ^ 40 * 3080896 * 2
def baseEnd_3080896 : Nat := 1581980494514483213931223

theorem tailTrace_3080896 : CollatzResearch.WordTrace tailWord_3080896 prefixEnd_3080896 1581980494514483213931223 := by
  unfold tailWord_3080896
  simp only [CollatzResearch.WordTrace]
  refine ⟨56184754323223720995483271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74913005764298294660644361 56184754323223720995483271)
  ·
    refine ⟨84277131484835581493224907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56184754323223720995483271 84277131484835581493224907)
    ·
      refine ⟨126415697227253372239837361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84277131484835581493224907 126415697227253372239837361)
      ·
        refine ⟨94811772920440029179878021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126415697227253372239837361 94811772920440029179878021)
        ·
          refine ⟨17777207422582505471227129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94811772920440029179878021 17777207422582505471227129)
          ·
            refine ⟨13332905566936879103420347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17777207422582505471227129 13332905566936879103420347)
            ·
              refine ⟨19999358350405318655130521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13332905566936879103420347 19999358350405318655130521)
              ·
                refine ⟨14999518762803988991347891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19999358350405318655130521 14999518762803988991347891)
                ·
                  refine ⟨22499278144205983487021837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14999518762803988991347891 22499278144205983487021837)
                  ·
                    refine ⟨8437229304077243807633189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22499278144205983487021837 8437229304077243807633189)
                    ·
                      refine ⟨1581980494514483213931223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8437229304077243807633189 1581980494514483213931223)
                      ·
                        rfl

theorem cell23_3080896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_3080896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080896 prefixEnd_3080896 := by exact prefixLift 3080896
  have htrace : WordTrace (prefixWord ++ tailWord_3080896) baseStart_3080896 baseEnd_3080896 := by
    simpa [prefixWord, tailWord_3080896, baseEnd_3080896] using wordTrace_append hprefix tailTrace_3080896
  have hstable : (prefixWord ++ tailWord_3080896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080896).length < 2 ^ (prefixWord ++ tailWord_3080896).sum := by decide
  have hdescent : baseEnd_3080896 < baseStart_3080896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080933 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_3080933 : Nat := 118140960795 + 3080933 * 2 ^ 59
def prefixEnd_3080933 : Nat := 4983230072969 + 3 ^ 40 * 3080933 * 2
def baseEnd_3080933 : Nat := 1581999493298699569168553

theorem tailTrace_3080933 : CollatzResearch.WordTrace tailWord_3080933 prefixEnd_3080933 1581999493298699569168553 := by
  unfold tailWord_3080933
  simp only [CollatzResearch.WordTrace]
  refine ⟨112370858147313397310063453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74913905431542264873375635 112370858147313397310063453)
  ·
    refine ⟨42139071805242523991273795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112370858147313397310063453 42139071805242523991273795)
    ·
      refine ⟨63208607707863785986910693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42139071805242523991273795 63208607707863785986910693)
      ·
        refine ⟨11851613945224459872545755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63208607707863785986910693 11851613945224459872545755)
        ·
          refine ⟨17777420917836689808818633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11851613945224459872545755 17777420917836689808818633)
          ·
            refine ⟨13333065688377517356613975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17777420917836689808818633 13333065688377517356613975)
            ·
              refine ⟨19999598532566276034920963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13333065688377517356613975 19999598532566276034920963)
              ·
                refine ⟨29999397798849414052381445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19999598532566276034920963 29999397798849414052381445)
                ·
                  refine ⟨5624887087284265134821521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29999397798849414052381445 5624887087284265134821521)
                  ·
                    refine ⟨4218665315463198851116141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5624887087284265134821521 4218665315463198851116141)
                    ·
                      refine ⟨1581999493298699569168553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4218665315463198851116141 1581999493298699569168553)
                      ·
                        rfl

theorem cell23_3080933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_3080933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080933 prefixEnd_3080933 := by exact prefixLift 3080933
  have htrace : WordTrace (prefixWord ++ tailWord_3080933) baseStart_3080933 baseEnd_3080933 := by
    simpa [prefixWord, tailWord_3080933, baseEnd_3080933] using wordTrace_append hprefix tailTrace_3080933
  have hstable : (prefixWord ++ tailWord_3080933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080933).length < 2 ^ (prefixWord ++ tailWord_3080933).sum := by decide
  have hdescent : baseEnd_3080933 < baseStart_3080933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080963 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 3]
def baseStart_3080963 : Nat := 118140960795 + 3080963 * 2 ^ 59
def prefixEnd_3080963 : Nat := 4983230072969 + 3 ^ 40 * 3080963 * 2
def baseEnd_3080963 : Nat := 1582014897718334451793415

theorem tailTrace_3080963 : CollatzResearch.WordTrace tailWord_3080963 prefixEnd_3080963 1582014897718334451793415 := by
  unfold tailWord_3080963
  simp only [CollatzResearch.WordTrace]
  refine ⟨112371952337204712433655543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74914634891469808289103695 112371952337204712433655543)
  ·
    refine ⟨168557928505807068650483315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112371952337204712433655543 168557928505807068650483315)
    ·
      refine ⟨252836892758710602975724973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168557928505807068650483315 252836892758710602975724973)
      ·
        refine ⟨94813834784516476115896865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252836892758710602975724973 94813834784516476115896865)
        ·
          refine ⟨71110376088387357086922649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94813834784516476115896865 71110376088387357086922649)
          ·
            refine ⟨53332782066290517815191987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71110376088387357086922649 53332782066290517815191987)
            ·
              refine ⟨79999173099435776722787981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53332782066290517815191987 79999173099435776722787981)
              ·
                refine ⟨29999689912288416271045493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79999173099435776722787981 29999689912288416271045493)
                ·
                  refine ⟨2812470929277039025410515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29999689912288416271045493 2812470929277039025410515)
                  ·
                    refine ⟨4218706393915558538115773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2812470929277039025410515 4218706393915558538115773)
                    ·
                      refine ⟨1582014897718334451793415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4218706393915558538115773 1582014897718334451793415)
                      ·
                        rfl

theorem cell23_3080963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_3080963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080963 prefixEnd_3080963 := by exact prefixLift 3080963
  have htrace : WordTrace (prefixWord ++ tailWord_3080963) baseStart_3080963 baseEnd_3080963 := by
    simpa [prefixWord, tailWord_3080963, baseEnd_3080963] using wordTrace_append hprefix tailTrace_3080963
  have hstable : (prefixWord ++ tailWord_3080963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080963).length < 2 ^ (prefixWord ++ tailWord_3080963).sum := by decide
  have hdescent : baseEnd_3080963 < baseStart_3080963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3080997 : List Nat := [1, 3, 1, 2, 3, 1, 3, 4, 1, 1, 3]
def baseStart_3080997 : Nat := 118140960795 + 3080997 * 2 ^ 59
def prefixEnd_3080997 : Nat := 4983230072969 + 3 ^ 40 * 3080997 * 2
def baseEnd_3080997 : Nat := 1582032356060587318768259

theorem tailTrace_3080997 : CollatzResearch.WordTrace tailWord_3080997 prefixEnd_3080997 1582032356060587318768259 := by
  unfold tailWord_3080997
  simp only [CollatzResearch.WordTrace]
  refine ⟨112373192419081536240393245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74915461612721024160262163 112373192419081536240393245)
  ·
    refine ⟨42139947157155576090147467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112373192419081536240393245 42139947157155576090147467)
    ·
      refine ⟨63209920735733364135221201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42139947157155576090147467 63209920735733364135221201)
      ·
        refine ⟨47407440551800023101415901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63209920735733364135221201 47407440551800023101415901)
        ·
          refine ⟨17777790206925008663030963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47407440551800023101415901 17777790206925008663030963)
          ·
            refine ⟨26666685310387512994546445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17777790206925008663030963 26666685310387512994546445)
            ·
              refine ⟨10000006991395317372954917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26666685310387512994546445 10000006991395317372954917)
              ·
                refine ⟨1875001310886622007429047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10000006991395317372954917 1875001310886622007429047)
                ·
                  refine ⟨2812501966329933011143571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875001310886622007429047 2812501966329933011143571)
                  ·
                    refine ⟨4218752949494899516715357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2812501966329933011143571 4218752949494899516715357)
                    ·
                      refine ⟨1582032356060587318768259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4218752949494899516715357 1582032356060587318768259)
                      ·
                        rfl

theorem cell23_3080997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_3080997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3080997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3080997 prefixEnd_3080997 := by exact prefixLift 3080997
  have htrace : WordTrace (prefixWord ++ tailWord_3080997) baseStart_3080997 baseEnd_3080997 := by
    simpa [prefixWord, tailWord_3080997, baseEnd_3080997] using wordTrace_append hprefix tailTrace_3080997
  have hstable : (prefixWord ++ tailWord_3080997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3080997).length < 2 ^ (prefixWord ++ tailWord_3080997).sum := by decide
  have hdescent : baseEnd_3080997 < baseStart_3080997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3080997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081013 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_3081013 : Nat := 118140960795 + 3081013 * 2 ^ 59
def prefixEnd_3081013 : Nat := 4983230072969 + 3 ^ 40 * 3081013 * 2
def baseEnd_3081013 : Nat := 527346857250353085389395

theorem tailTrace_3081013 : CollatzResearch.WordTrace tailWord_3081013 prefixEnd_3081013 527346857250353085389395 := by
  unfold tailWord_3081013
  simp only [CollatzResearch.WordTrace]
  refine ⟨112373775987023570972975693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74915850658015713981983795 112373775987023570972975693)
  ·
    refine ⟨42140165995133839114865885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112373775987023570972975693 42140165995133839114865885)
    ·
      refine ⟨15802562248175189668074707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42140165995133839114865885 15802562248175189668074707)
      ·
        refine ⟨23703843372262784502112061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15802562248175189668074707 23703843372262784502112061)
        ·
          refine ⟨8888941264598544188292023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23703843372262784502112061 8888941264598544188292023)
          ·
            refine ⟨13333411896897816282438035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8888941264598544188292023 13333411896897816282438035)
            ·
              refine ⟨20000117845346724423657053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13333411896897816282438035 20000117845346724423657053)
              ·
                refine ⟨7500044192005021658871395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20000117845346724423657053 7500044192005021658871395)
                ·
                  refine ⟨11250066288007532488307093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7500044192005021658871395 11250066288007532488307093)
                  ·
                    refine ⟨527346857250353085389395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11250066288007532488307093 527346857250353085389395)
                    ·
                      rfl

theorem cell23_3081013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_3081013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081013 prefixEnd_3081013 := by exact prefixLift 3081013
  have htrace : WordTrace (prefixWord ++ tailWord_3081013) baseStart_3081013 baseEnd_3081013 := by
    simpa [prefixWord, tailWord_3081013, baseEnd_3081013] using wordTrace_append hprefix tailTrace_3081013
  have hstable : (prefixWord ++ tailWord_3081013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081013).length < 2 ^ (prefixWord ++ tailWord_3081013).sum := by decide
  have hdescent : baseEnd_3081013 < baseStart_3081013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081014 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3081014 : Nat := 118140960795 + 3081014 * 2 ^ 59
def prefixEnd_3081014 : Nat := 4983230072969 + 3 ^ 40 * 3081014 * 2
def baseEnd_3081014 : Nat := 1582041085231713752255681

theorem tailTrace_3081014 : CollatzResearch.WordTrace tailWord_3081014 prefixEnd_3081014 1582041085231713752255681 := by
  unfold tailWord_3081014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7023363278751246758985131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74915874973346632095841397 7023363278751246758985131)
  ·
    refine ⟨10535044918126870138477697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7023363278751246758985131 10535044918126870138477697)
    ·
      refine ⟨7901283688595152603858273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10535044918126870138477697 7901283688595152603858273)
      ·
        refine ⟨5925962766446364452893705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7901283688595152603858273 5925962766446364452893705)
        ·
          refine ⟨4444472074834773339670279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5925962766446364452893705 4444472074834773339670279)
          ·
            refine ⟨6666708112252160009505419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444472074834773339670279 6666708112252160009505419)
            ·
              refine ⟨10000062168378240014258129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6666708112252160009505419 10000062168378240014258129)
              ·
                refine ⟨7500046626283680010693597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10000062168378240014258129 7500046626283680010693597)
                ·
                  refine ⟨2812517484856380004010099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7500046626283680010693597 2812517484856380004010099)
                  ·
                    refine ⟨4218776227284570006015149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2812517484856380004010099 4218776227284570006015149)
                    ·
                      refine ⟨1582041085231713752255681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4218776227284570006015149 1582041085231713752255681)
                      ·
                        rfl

theorem cell23_3081014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3081014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081014 prefixEnd_3081014 := by exact prefixLift 3081014
  have htrace : WordTrace (prefixWord ++ tailWord_3081014) baseStart_3081014 baseEnd_3081014 := by
    simpa [prefixWord, tailWord_3081014, baseEnd_3081014] using wordTrace_append hprefix tailTrace_3081014
  have hstable : (prefixWord ++ tailWord_3081014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081014).length < 2 ^ (prefixWord ++ tailWord_3081014).sum := by decide
  have hdescent : baseEnd_3081014 < baseStart_3081014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081033 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_3081033 : Nat := 118140960795 + 3081033 * 2 ^ 59
def prefixEnd_3081033 : Nat := 4983230072969 + 3 ^ 40 * 3081033 * 2
def baseEnd_3081033 : Nat := 1582050841364149177918093

theorem tailTrace_3081033 : CollatzResearch.WordTrace tailWord_3081033 prefixEnd_3081033 1582050841364149177918093 := by
  unfold tailWord_3081033
  simp only [CollatzResearch.WordTrace]
  refine ⟨112374505446951114388703753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74916336964634076259135835 112374505446951114388703753)
  ·
    refine ⟨84280879085213335791527815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112374505446951114388703753 84280879085213335791527815)
    ·
      refine ⟨126421318627820003687291723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84280879085213335791527815 126421318627820003687291723)
      ·
        refine ⟨189631977941730005530937585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126421318627820003687291723 189631977941730005530937585)
        ·
          refine ⟨142223983456297504148203189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189631977941730005530937585 142223983456297504148203189)
          ·
            refine ⟨13333498449027891013894049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142223983456297504148203189 13333498449027891013894049)
            ·
              refine ⟨10000123836770918260420537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13333498449027891013894049 10000123836770918260420537)
              ·
                refine ⟨7500092877578188695315403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10000123836770918260420537 7500092877578188695315403)
                ·
                  refine ⟨11250139316367283042973105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7500092877578188695315403 11250139316367283042973105)
                  ·
                    refine ⟨8437604487275462282229829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11250139316367283042973105 8437604487275462282229829)
                    ·
                      refine ⟨1582050841364149177918093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8437604487275462282229829 1582050841364149177918093)
                      ·
                        rfl

theorem cell23_3081033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_3081033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081033 prefixEnd_3081033 := by exact prefixLift 3081033
  have htrace : WordTrace (prefixWord ++ tailWord_3081033) baseStart_3081033 baseEnd_3081033 := by
    simpa [prefixWord, tailWord_3081033, baseEnd_3081033] using wordTrace_append hprefix tailTrace_3081033
  have hstable : (prefixWord ++ tailWord_3081033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081033).length < 2 ^ (prefixWord ++ tailWord_3081033).sum := by decide
  have hdescent : baseEnd_3081033 < baseStart_3081033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081047 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 2, 4]
def baseStart_3081047 : Nat := 118140960795 + 3081047 * 2 ^ 59
def prefixEnd_3081047 : Nat := 4983230072969 + 3 ^ 40 * 3081047 * 2
def baseEnd_3081047 : Nat := 527352676697770707714343

theorem tailTrace_3081047 : CollatzResearch.WordTrace tailWord_3081047 prefixEnd_3081047 527352676697770707714343 := by
  unfold tailWord_3081047
  simp only [CollatzResearch.WordTrace]
  refine ⟨112375016068900394779713395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74916677379266929853142263 112375016068900394779713395)
  ·
    refine ⟨168562524103350592169570093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112375016068900394779713395 168562524103350592169570093)
    ·
      refine ⟨63210946538756472063588785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168562524103350592169570093 63210946538756472063588785)
      ·
        refine ⟨47408209904067354047691589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63210946538756472063588785 47408209904067354047691589)
        ·
          refine ⟨8889039357012628883942173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47408209904067354047691589 8889039357012628883942173)
          ·
            refine ⟨3333389758879735831478315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8889039357012628883942173 3333389758879735831478315)
            ·
              refine ⟨5000084638319603747217473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3333389758879735831478315 5000084638319603747217473)
              ·
                refine ⟨3750063478739702810413105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5000084638319603747217473 3750063478739702810413105)
                ·
                  refine ⟨2812547609054777107809829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3750063478739702810413105 2812547609054777107809829)
                  ·
                    refine ⟨527352676697770707714343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2812547609054777107809829 527352676697770707714343)
                    ·
                      rfl

theorem cell23_3081047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_3081047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081047 prefixEnd_3081047 := by exact prefixLift 3081047
  have htrace : WordTrace (prefixWord ++ tailWord_3081047) baseStart_3081047 baseEnd_3081047 := by
    simpa [prefixWord, tailWord_3081047, baseEnd_3081047] using wordTrace_append hprefix tailTrace_3081047
  have hstable : (prefixWord ++ tailWord_3081047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081047).length < 2 ^ (prefixWord ++ tailWord_3081047).sum := by decide
  have hdescent : baseEnd_3081047 < baseStart_3081047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081097 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 1, 3, 2]
def baseStart_3081097 : Nat := 118140960795 + 3081097 * 2 ^ 59
def prefixEnd_3081097 : Nat := 4983230072969 + 3 ^ 40 * 3081097 * 2
def baseEnd_3081097 : Nat := 1582083704126036927517799

theorem tailTrace_3081097 : CollatzResearch.WordTrace tailWord_3081097 prefixEnd_3081097 1582083704126036927517799 := by
  unfold tailWord_3081097
  simp only [CollatzResearch.WordTrace]
  refine ⟨112376839718719253319033545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74917893145812835546022363 112376839718719253319033545)
  ·
    refine ⟨84282629789039439989275159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112376839718719253319033545 84282629789039439989275159)
    ·
      refine ⟨126423944683559159983912739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84282629789039439989275159 126423944683559159983912739)
      ·
        refine ⟨189635917025338739975869109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126423944683559159983912739 189635917025338739975869109)
        ·
          refine ⟨17778367221125506872737729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189635917025338739975869109 17778367221125506872737729)
          ·
            refine ⟨13333775415844130154553297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17778367221125506872737729 13333775415844130154553297)
            ·
              refine ⟨10000331561883097615914973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13333775415844130154553297 10000331561883097615914973)
              ·
                refine ⟨3750124335706161605968115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10000331561883097615914973 3750124335706161605968115)
                ·
                  refine ⟨5625186503559242408952173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750124335706161605968115 5625186503559242408952173)
                  ·
                    refine ⟨2109444938834715903357065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5625186503559242408952173 2109444938834715903357065)
                    ·
                      refine ⟨1582083704126036927517799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109444938834715903357065 1582083704126036927517799)
                      ·
                        rfl

theorem cell23_3081097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 3, 2].length) (baseStart_3081097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081097 prefixEnd_3081097 := by exact prefixLift 3081097
  have htrace : WordTrace (prefixWord ++ tailWord_3081097) baseStart_3081097 baseEnd_3081097 := by
    simpa [prefixWord, tailWord_3081097, baseEnd_3081097] using wordTrace_append hprefix tailTrace_3081097
  have hstable : (prefixWord ++ tailWord_3081097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081097).length < 2 ^ (prefixWord ++ tailWord_3081097).sum := by decide
  have hdescent : baseEnd_3081097 < baseStart_3081097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081113 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 3]
def baseStart_3081113 : Nat := 118140960795 + 3081113 * 2 ^ 59
def prefixEnd_3081113 : Nat := 4983230072969 + 3 ^ 40 * 3081113 * 2
def baseEnd_3081113 : Nat := 1582091919816508864917725

theorem tailTrace_3081113 : CollatzResearch.WordTrace tailWord_3081113 prefixEnd_3081113 1582091919816508864917725 := by
  unfold tailWord_3081113
  simp only [CollatzResearch.WordTrace]
  refine ⟨112377423286661288051615993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74918282191107525367743995 112377423286661288051615993)
  ·
    refine ⟨84283067464995966038711995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112377423286661288051615993 84283067464995966038711995)
    ·
      refine ⟨126424601197493949058067993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84283067464995966038711995 126424601197493949058067993)
      ·
        refine ⟨94818450898120461793550995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126424601197493949058067993 94818450898120461793550995)
        ·
          refine ⟨142227676347180692690326493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94818450898120461793550995 142227676347180692690326493)
          ·
            refine ⟨53335378630192759758872435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142227676347180692690326493 53335378630192759758872435)
            ·
              refine ⟨80003067945289139638308653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53335378630192759758872435 80003067945289139638308653)
              ·
                refine ⟨30001150479483427364365745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80003067945289139638308653 30001150479483427364365745)
                ·
                  refine ⟨22500862859612570523274309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30001150479483427364365745 22500862859612570523274309)
                  ·
                    refine ⟨4218911786177356973113933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22500862859612570523274309 4218911786177356973113933)
                    ·
                      refine ⟨1582091919816508864917725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4218911786177356973113933 1582091919816508864917725)
                      ·
                        rfl

theorem cell23_3081113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_3081113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081113 prefixEnd_3081113 := by exact prefixLift 3081113
  have htrace : WordTrace (prefixWord ++ tailWord_3081113) baseStart_3081113 baseEnd_3081113 := by
    simpa [prefixWord, tailWord_3081113, baseEnd_3081113] using wordTrace_append hprefix tailTrace_3081113
  have hstable : (prefixWord ++ tailWord_3081113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081113).length < 2 ^ (prefixWord ++ tailWord_3081113).sum := by decide
  have hdescent : baseEnd_3081113 < baseStart_3081113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081121 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3081121 : Nat := 118140960795 + 3081121 * 2 ^ 59
def prefixEnd_3081121 : Nat := 4983230072969 + 3 ^ 40 * 3081121 * 2
def baseEnd_3081121 : Nat := 1582096027661744833617689

theorem tailTrace_3081121 : CollatzResearch.WordTrace tailWord_3081121 prefixEnd_3081121 1582096027661744833617689 := by
  unfold tailWord_3081121
  simp only [CollatzResearch.WordTrace]
  refine ⟨112377715070632305417907217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74918476713754870278604811 112377715070632305417907217)
  ·
    refine ⟨84283286302974229063430413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112377715070632305417907217 84283286302974229063430413)
    ·
      refine ⟨31606232363615335898786405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84283286302974229063430413 31606232363615335898786405)
      ·
        refine ⟨5926168568177875481022451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31606232363615335898786405 5926168568177875481022451)
        ·
          refine ⟨8889252852266813221533677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5926168568177875481022451 8889252852266813221533677)
          ·
            refine ⟨3333469819600054958075129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8889252852266813221533677 3333469819600054958075129)
            ·
              refine ⟨2500102364700041218556347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3333469819600054958075129 2500102364700041218556347)
              ·
                refine ⟨3750153547050061827834521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500102364700041218556347 3750153547050061827834521)
                ·
                  refine ⟨2812615160287546370875891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3750153547050061827834521 2812615160287546370875891)
                  ·
                    refine ⟨4218922740431319556313837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2812615160287546370875891 4218922740431319556313837)
                    ·
                      refine ⟨1582096027661744833617689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4218922740431319556313837 1582096027661744833617689)
                      ·
                        rfl

theorem cell23_3081121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3081121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081121 prefixEnd_3081121 := by exact prefixLift 3081121
  have htrace : WordTrace (prefixWord ++ tailWord_3081121) baseStart_3081121 baseEnd_3081121 := by
    simpa [prefixWord, tailWord_3081121, baseEnd_3081121] using wordTrace_append hprefix tailTrace_3081121
  have hstable : (prefixWord ++ tailWord_3081121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081121).length < 2 ^ (prefixWord ++ tailWord_3081121).sum := by decide
  have hdescent : baseEnd_3081121 < baseStart_3081121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081123 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 4]
def baseStart_3081123 : Nat := 118140960795 + 3081123 * 2 ^ 59
def prefixEnd_3081123 : Nat := 4983230072969 + 3 ^ 40 * 3081123 * 2
def baseEnd_3081123 : Nat := 1582097054623053825792679

theorem tailTrace_3081123 : CollatzResearch.WordTrace tailWord_3081123 prefixEnd_3081123 1582097054623053825792679 := by
  unfold tailWord_3081123
  simp only [CollatzResearch.WordTrace]
  refine ⟨112377788016625059759480023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74918525344416706506320015 112377788016625059759480023)
  ·
    refine ⟨168566682024937589639220035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112377788016625059759480023 168566682024937589639220035)
    ·
      refine ⟨252850023037406384458830053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168566682024937589639220035 252850023037406384458830053)
      ·
        refine ⟨47409379319513697086030635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252850023037406384458830053 47409379319513697086030635)
        ·
          refine ⟨71114068979270545629045953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47409379319513697086030635 71114068979270545629045953)
          ·
            refine ⟨53335551734452909221784465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71114068979270545629045953 53335551734452909221784465)
            ·
              refine ⟨40001663800839681916338349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53335551734452909221784465 40001663800839681916338349)
              ·
                refine ⟨15000623925314880718626881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40001663800839681916338349 15000623925314880718626881)
                ·
                  refine ⟨11250467943986160538970161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15000623925314880718626881 11250467943986160538970161)
                  ·
                    refine ⟨8437850957989620404227621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11250467943986160538970161 8437850957989620404227621)
                    ·
                      refine ⟨1582097054623053825792679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8437850957989620404227621 1582097054623053825792679)
                      ·
                        rfl

theorem cell23_3081123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_3081123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081123 prefixEnd_3081123 := by exact prefixLift 3081123
  have htrace : WordTrace (prefixWord ++ tailWord_3081123) baseStart_3081123 baseEnd_3081123 := by
    simpa [prefixWord, tailWord_3081123, baseEnd_3081123] using wordTrace_append hprefix tailTrace_3081123
  have hstable : (prefixWord ++ tailWord_3081123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081123).length < 2 ^ (prefixWord ++ tailWord_3081123).sum := by decide
  have hdescent : baseEnd_3081123 < baseStart_3081123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081167 : List Nat := [1, 1, 2, 1, 1, 6, 4, 2, 5]
def baseStart_3081167 : Nat := 118140960795 + 3081167 * 2 ^ 59
def prefixEnd_3081167 : Nat := 4983230072969 + 3 ^ 40 * 3081167 * 2
def baseEnd_3081167 : Nat := 175791071974650183738053

theorem tailTrace_3081167 : CollatzResearch.WordTrace tailWord_3081167 prefixEnd_3081167 175791071974650183738053 := by
  unfold tailWord_3081167
  simp only [CollatzResearch.WordTrace]
  refine ⟨112379392828465655274081755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74919595218977103516054503 112379392828465655274081755)
  ·
    refine ⟨168569089242698482911122633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112379392828465655274081755 168569089242698482911122633)
    ·
      refine ⟨126426816932023862183341975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168569089242698482911122633 126426816932023862183341975)
      ·
        refine ⟨189640225398035793275012963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126426816932023862183341975 189640225398035793275012963)
        ·
          refine ⟨284460338097053689912519445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189640225398035793275012963 284460338097053689912519445)
          ·
            refine ⟨13334078348299391714649349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 284460338097053689912519445 13334078348299391714649349)
            ·
              refine ⟨2500139690306135946496753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13334078348299391714649349 2500139690306135946496753)
              ·
                refine ⟨1875104767729601959872565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500139690306135946496753 1875104767729601959872565)
                ·
                  refine ⟨175791071974650183738053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1875104767729601959872565 175791071974650183738053)
                  ·
                    rfl

theorem cell23_3081167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 5].length) (baseStart_3081167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081167 prefixEnd_3081167 := by exact prefixLift 3081167
  have htrace : WordTrace (prefixWord ++ tailWord_3081167) baseStart_3081167 baseEnd_3081167 := by
    simpa [prefixWord, tailWord_3081167, baseEnd_3081167] using wordTrace_append hprefix tailTrace_3081167
  have hstable : (prefixWord ++ tailWord_3081167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081167).length < 2 ^ (prefixWord ++ tailWord_3081167).sum := by decide
  have hdescent : baseEnd_3081167 < baseStart_3081167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081200 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 3, 6, 2]
def baseStart_3081200 : Nat := 118140960795 + 3081200 * 2 ^ 59
def prefixEnd_3081200 : Nat := 4983230072969 + 3 ^ 40 * 3081200 * 2
def baseEnd_3081200 : Nat := 1582136592633450024529825

theorem tailTrace_3081200 : CollatzResearch.WordTrace tailWord_3081200 prefixEnd_3081200 1582136592633450024529825 := by
  unfold tailWord_3081200
  simp only [CollatzResearch.WordTrace]
  refine ⟨56190298218673050955016527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74920397624897401273355369 56190298218673050955016527)
  ·
    refine ⟨84285447328009576432524791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56190298218673050955016527 84285447328009576432524791)
    ·
      refine ⟨126428170992014364648787187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84285447328009576432524791 126428170992014364648787187)
      ·
        refine ⟨189642256488021546973180781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126428170992014364648787187 189642256488021546973180781)
        ·
          refine ⟨71115846183008080114942793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189642256488021546973180781 71115846183008080114942793)
          ·
            refine ⟨53336884637256060086207095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71115846183008080114942793 53336884637256060086207095)
            ·
              refine ⟨80005326955884090129310643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53336884637256060086207095 80005326955884090129310643)
              ·
                refine ⟨120007990433826135193965965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80005326955884090129310643 120007990433826135193965965)
                ·
                  refine ⟨45002996412684800697737237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120007990433826135193965965 45002996412684800697737237)
                  ·
                    refine ⟨2109515456844600032706433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45002996412684800697737237 2109515456844600032706433)
                    ·
                      refine ⟨1582136592633450024529825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109515456844600032706433 1582136592633450024529825)
                      ·
                        rfl

theorem cell23_3081200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 6, 2].length) (baseStart_3081200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081200 prefixEnd_3081200 := by exact prefixLift 3081200
  have htrace : WordTrace (prefixWord ++ tailWord_3081200) baseStart_3081200 baseEnd_3081200 := by
    simpa [prefixWord, tailWord_3081200, baseEnd_3081200] using wordTrace_append hprefix tailTrace_3081200
  have hstable : (prefixWord ++ tailWord_3081200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081200).length < 2 ^ (prefixWord ++ tailWord_3081200).sum := by decide
  have hdescent : baseEnd_3081200 < baseStart_3081200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081217 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_3081217 : Nat := 118140960795 + 3081217 * 2 ^ 59
def prefixEnd_3081217 : Nat := 4983230072969 + 3 ^ 40 * 3081217 * 2
def baseEnd_3081217 : Nat := 1582145321804576458017247

theorem tailTrace_3081217 : CollatzResearch.WordTrace tailWord_3081217 prefixEnd_3081217 1582145321804576458017247 := by
  unfold tailWord_3081217
  simp only [CollatzResearch.WordTrace]
  refine ⟨112381216478284513813401905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74920810985523009208934603 112381216478284513813401905)
  ·
    refine ⟨84285912358713385360051429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112381216478284513813401905 84285912358713385360051429)
    ·
      refine ⟨15803608567258759755009643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84285912358713385360051429 15803608567258759755009643)
      ·
        refine ⟨23705412850888139632514465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15803608567258759755009643 23705412850888139632514465)
        ·
          refine ⟨17779059638166104724385849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23705412850888139632514465 17779059638166104724385849)
          ·
            refine ⟨13334294728624578543289387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17779059638166104724385849 13334294728624578543289387)
            ·
              refine ⟨20001442092936867814934081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13334294728624578543289387 20001442092936867814934081)
              ·
                refine ⟨15001081569702650861200561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20001442092936867814934081 15001081569702650861200561)
                ·
                  refine ⟨11250811177276988145900421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15001081569702650861200561 11250811177276988145900421)
                  ·
                    refine ⟨2109527095739435277356329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11250811177276988145900421 2109527095739435277356329)
                    ·
                      refine ⟨1582145321804576458017247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109527095739435277356329 1582145321804576458017247)
                      ·
                        rfl

theorem cell23_3081217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_3081217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081217 prefixEnd_3081217 := by exact prefixLift 3081217
  have htrace : WordTrace (prefixWord ++ tailWord_3081217) baseStart_3081217 baseEnd_3081217 := by
    simpa [prefixWord, tailWord_3081217, baseEnd_3081217] using wordTrace_append hprefix tailTrace_3081217
  have hstable : (prefixWord ++ tailWord_3081217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081217).length < 2 ^ (prefixWord ++ tailWord_3081217).sum := by decide
  have hdescent : baseEnd_3081217 < baseStart_3081217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081227 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 3, 4]
def baseStart_3081227 : Nat := 118140960795 + 3081227 * 2 ^ 59
def prefixEnd_3081227 : Nat := 4983230072969 + 3 ^ 40 * 3081227 * 2
def baseEnd_3081227 : Nat := 527383485537040472964067

theorem tailTrace_3081227 : CollatzResearch.WordTrace tailWord_3081227 prefixEnd_3081227 527383485537040472964067 := by
  unfold tailWord_3081227
  simp only [CollatzResearch.WordTrace]
  refine ⟨112381581208248285521265935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74921054138832190347510623 112381581208248285521265935)
  ·
    refine ⟨168572371812372428281898903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112381581208248285521265935 168572371812372428281898903)
    ·
      refine ⟨252858557718558642422848355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168572371812372428281898903 252858557718558642422848355)
      ·
        refine ⟨379287836577837963634272533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252858557718558642422848355 379287836577837963634272533)
        ·
          refine ⟨17779117339586154545356525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 379287836577837963634272533 17779117339586154545356525)
          ·
            refine ⟨6667169002344807954508697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17779117339586154545356525 6667169002344807954508697)
            ·
              refine ⟨5000376751758605965881523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667169002344807954508697 5000376751758605965881523)
              ·
                refine ⟨7500565127637908948822285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5000376751758605965881523 7500565127637908948822285)
                ·
                  refine ⟨2812711922864215855808357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7500565127637908948822285 2812711922864215855808357)
                  ·
                    refine ⟨527383485537040472964067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2812711922864215855808357 527383485537040472964067)
                    ·
                      rfl

theorem cell23_3081227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 4].length) (baseStart_3081227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081227 prefixEnd_3081227 := by exact prefixLift 3081227
  have htrace : WordTrace (prefixWord ++ tailWord_3081227) baseStart_3081227 baseEnd_3081227 := by
    simpa [prefixWord, tailWord_3081227, baseEnd_3081227] using wordTrace_append hprefix tailTrace_3081227
  have hstable : (prefixWord ++ tailWord_3081227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081227).length < 2 ^ (prefixWord ++ tailWord_3081227).sum := by decide
  have hdescent : baseEnd_3081227 < baseStart_3081227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081263 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_3081263 : Nat := 118140960795 + 3081263 * 2 ^ 59
def prefixEnd_3081263 : Nat := 4983230072969 + 3 ^ 40 * 3081263 * 2
def baseEnd_3081263 : Nat := 1582168941914683278042035

theorem tailTrace_3081263 : CollatzResearch.WordTrace tailWord_3081263 prefixEnd_3081263 1582168941914683278042035 := by
  unfold tailWord_3081263
  simp only [CollatzResearch.WordTrace]
  refine ⟨112382894236117863669576443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74921929490745242446384295 112382894236117863669576443)
  ·
    refine ⟨168574341354176795504364665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112382894236117863669576443 168574341354176795504364665)
    ·
      refine ⟨126430756015632596628273499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168574341354176795504364665 126430756015632596628273499)
      ·
        refine ⟨189646134023448894942410249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126430756015632596628273499 189646134023448894942410249)
        ·
          refine ⟨142234600517586671206807687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189646134023448894942410249 142234600517586671206807687)
          ·
            refine ⟨213351900776380006810211531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142234600517586671206807687 213351900776380006810211531)
            ·
              refine ⟨320027851164570010215317297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213351900776380006810211531 320027851164570010215317297)
              ·
                refine ⟨240020888373427507661487973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320027851164570010215317297 240020888373427507661487973)
                ·
                  refine ⟨45003916570017657686528995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240020888373427507661487973 45003916570017657686528995)
                  ·
                    refine ⟨67505874855026486529793493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45003916570017657686528995 67505874855026486529793493)
                    ·
                      refine ⟨1582168941914683278042035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67505874855026486529793493 1582168941914683278042035)
                      ·
                        rfl

theorem cell23_3081263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_3081263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081263 prefixEnd_3081263 := by exact prefixLift 3081263
  have htrace : WordTrace (prefixWord ++ tailWord_3081263) baseStart_3081263 baseEnd_3081263 := by
    simpa [prefixWord, tailWord_3081263, baseEnd_3081263] using wordTrace_append hprefix tailTrace_3081263
  have hstable : (prefixWord ++ tailWord_3081263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081263).length < 2 ^ (prefixWord ++ tailWord_3081263).sum := by decide
  have hdescent : baseEnd_3081263 < baseStart_3081263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081278 : List Nat := [4, 2, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_3081278 : Nat := 118140960795 + 3081278 * 2 ^ 59
def prefixEnd_3081278 : Nat := 4983230072969 + 3 ^ 40 * 3081278 * 2
def baseEnd_3081278 : Nat := 527392214708166906451489

theorem tailTrace_3081278 : CollatzResearch.WordTrace tailWord_3081278 prefixEnd_3081278 527392214708166906451489 := by
  unfold tailWord_3081278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14047930166382940153921561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74922294220709014154248325 14047930166382940153921561)
  ·
    refine ⟨10535947624787205115441171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14047930166382940153921561 10535947624787205115441171)
    ·
      refine ⟨15803921437180807673161757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10535947624787205115441171 15803921437180807673161757)
      ·
        refine ⟨5926470538942802877435659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15803921437180807673161757 5926470538942802877435659)
        ·
          refine ⟨8889705808414204316153489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5926470538942802877435659 8889705808414204316153489)
          ·
            refine ⟨6667279356310653237115117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8889705808414204316153489 6667279356310653237115117)
            ·
              refine ⟨2500229758616494963918169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6667279356310653237115117 2500229758616494963918169)
              ·
                refine ⟨1875172318962371222938627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500229758616494963918169 1875172318962371222938627)
                ·
                  refine ⟨2812758478443556834407941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875172318962371222938627 2812758478443556834407941)
                  ·
                    refine ⟨527392214708166906451489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2812758478443556834407941 527392214708166906451489)
                    ·
                      rfl

theorem cell23_3081278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_3081278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081278 prefixEnd_3081278 := by exact prefixLift 3081278
  have htrace : WordTrace (prefixWord ++ tailWord_3081278) baseStart_3081278 baseEnd_3081278 := by
    simpa [prefixWord, tailWord_3081278, baseEnd_3081278] using wordTrace_append hprefix tailTrace_3081278
  have hstable : (prefixWord ++ tailWord_3081278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081278).length < 2 ^ (prefixWord ++ tailWord_3081278).sum := by decide
  have hdescent : baseEnd_3081278 < baseStart_3081278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081324 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 4]
def baseStart_3081324 : Nat := 118140960795 + 3081324 * 2 ^ 59
def prefixEnd_3081324 : Nat := 4983230072969 + 3 ^ 40 * 3081324 * 2
def baseEnd_3081324 : Nat := 1582200264234607539379255

theorem tailTrace_3081324 : CollatzResearch.WordTrace tailWord_3081324 prefixEnd_3081324 1582200264234607539379255 := by
  unfold tailWord_3081324
  simp only [CollatzResearch.WordTrace]
  refine ⟨56192559544448435543773513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74923412725931247391698017 56192559544448435543773513)
  ·
    refine ⟨42144419658336326657830135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56192559544448435543773513 42144419658336326657830135)
    ·
      refine ⟨63216629487504489986745203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42144419658336326657830135 63216629487504489986745203)
      ·
        refine ⟨94824944231256734980117805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63216629487504489986745203 94824944231256734980117805)
        ·
          refine ⟨35559354086721275617544177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94824944231256734980117805 35559354086721275617544177)
          ·
            refine ⟨26669515565040956713158133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35559354086721275617544177 26669515565040956713158133)
            ·
              refine ⟨2500267084222589691858575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26669515565040956713158133 2500267084222589691858575)
              ·
                refine ⟨3750400626333884537787863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500267084222589691858575 3750400626333884537787863)
                ·
                  refine ⟨5625600939500826806681795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750400626333884537787863 5625600939500826806681795)
                  ·
                    refine ⟨8438401409251240210022693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5625600939500826806681795 8438401409251240210022693)
                    ·
                      refine ⟨1582200264234607539379255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8438401409251240210022693 1582200264234607539379255)
                      ·
                        rfl

theorem cell23_3081324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_3081324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081324 prefixEnd_3081324 := by exact prefixLift 3081324
  have htrace : WordTrace (prefixWord ++ tailWord_3081324) baseStart_3081324 baseEnd_3081324 := by
    simpa [prefixWord, tailWord_3081324, baseEnd_3081324] using wordTrace_append hprefix tailTrace_3081324
  have hstable : (prefixWord ++ tailWord_3081324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081324).length < 2 ^ (prefixWord ++ tailWord_3081324).sum := by decide
  have hdescent : baseEnd_3081324 < baseStart_3081324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081375 : List Nat := [1, 1, 2, 6, 2, 1, 2, 3, 1, 2, 2]
def baseStart_3081375 : Nat := 118140960795 + 3081375 * 2 ^ 59
def prefixEnd_3081375 : Nat := 4983230072969 + 3 ^ 40 * 3081375 * 2
def baseEnd_3081375 : Nat := 1582226451747986839841521

theorem tailTrace_3081375 : CollatzResearch.WordTrace tailWord_3081375 prefixEnd_3081375 1582226451747986839841521 := by
  unfold tailWord_3081375
  simp only [CollatzResearch.WordTrace]
  refine ⟨112386979211712106797653579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74924652807808071198435719 112386979211712106797653579)
  ·
    refine ⟨168580468817568160196480369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112386979211712106797653579 168580468817568160196480369)
    ·
      refine ⟨126435351613176120147360277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168580468817568160196480369 126435351613176120147360277)
      ·
        refine ⟨5926657106867630631907513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126435351613176120147360277 5926657106867630631907513)
        ·
          refine ⟨4444992830150722973930635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5926657106867630631907513 4444992830150722973930635)
          ·
            refine ⟨6667489245226084460895953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444992830150722973930635 6667489245226084460895953)
            ·
              refine ⟨5000616933919563345671965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667489245226084460895953 5000616933919563345671965)
              ·
                refine ⟨1875231350219836254626987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5000616933919563345671965 1875231350219836254626987)
                ·
                  refine ⟨2812847025329754381940481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875231350219836254626987 2812847025329754381940481)
                  ·
                    refine ⟨2109635268997315786455361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2812847025329754381940481 2109635268997315786455361)
                    ·
                      refine ⟨1582226451747986839841521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109635268997315786455361 1582226451747986839841521)
                      ·
                        rfl

theorem cell23_3081375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_3081375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081375 prefixEnd_3081375 := by exact prefixLift 3081375
  have htrace : WordTrace (prefixWord ++ tailWord_3081375) baseStart_3081375 baseEnd_3081375 := by
    simpa [prefixWord, tailWord_3081375, baseEnd_3081375] using wordTrace_append hprefix tailTrace_3081375
  have hstable : (prefixWord ++ tailWord_3081375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081375).length < 2 ^ (prefixWord ++ tailWord_3081375).sum := by decide
  have hdescent : baseEnd_3081375 < baseStart_3081375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081400 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_3081400 : Nat := 118140960795 + 3081400 * 2 ^ 59
def prefixEnd_3081400 : Nat := 4983230072969 + 3 ^ 40 * 3081400 * 2
def baseEnd_3081400 : Nat := 1582239288764349242028905

theorem tailTrace_3081400 : CollatzResearch.WordTrace tailWord_3081400 prefixEnd_3081400 1582239288764349242028905 := by
  unfold tailWord_3081400
  simp only [CollatzResearch.WordTrace]
  refine ⟨56193945518310768033656827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74925260691081024044875769 56193945518310768033656827)
  ·
    refine ⟨84290918277466152050485241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56193945518310768033656827 84290918277466152050485241)
    ·
      refine ⟨63218188708099614037863931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84290918277466152050485241 63218188708099614037863931)
      ·
        refine ⟨94827283062149421056795897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63218188708099614037863931 94827283062149421056795897)
        ·
          refine ⟨71120462296612065792596923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94827283062149421056795897 71120462296612065792596923)
          ·
            refine ⟨106680693444918098688895385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71120462296612065792596923 106680693444918098688895385)
            ·
              refine ⟨80010520083688574016671539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106680693444918098688895385 80010520083688574016671539)
              ·
                refine ⟨120015780125532861025007309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80010520083688574016671539 120015780125532861025007309)
                ·
                  refine ⟨45005917547074822884377741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120015780125532861025007309 45005917547074822884377741)
                  ·
                    refine ⟨16877219080153058581641653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45005917547074822884377741 16877219080153058581641653)
                    ·
                      refine ⟨1582239288764349242028905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16877219080153058581641653 1582239288764349242028905)
                      ·
                        rfl

theorem cell23_3081400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_3081400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081400 prefixEnd_3081400 := by exact prefixLift 3081400
  have htrace : WordTrace (prefixWord ++ tailWord_3081400) baseStart_3081400 baseEnd_3081400 := by
    simpa [prefixWord, tailWord_3081400, baseEnd_3081400] using wordTrace_append hprefix tailTrace_3081400
  have hstable : (prefixWord ++ tailWord_3081400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081400).length < 2 ^ (prefixWord ++ tailWord_3081400).sum := by decide
  have hdescent : baseEnd_3081400 < baseStart_3081400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081408 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 2, 1, 3]
def baseStart_3081408 : Nat := 118140960795 + 3081408 * 2 ^ 59
def prefixEnd_3081408 : Nat := 4983230072969 + 3 ^ 40 * 3081408 * 2
def baseEnd_3081408 : Nat := 1582243396609585210728869

theorem tailTrace_3081408 : CollatzResearch.WordTrace tailWord_3081408 prefixEnd_3081408 1582243396609585210728869 := by
  unfold tailWord_3081408
  simp only [CollatzResearch.WordTrace]
  refine ⟨56194091410296276716802439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74925455213728368955736585 56194091410296276716802439)
  ·
    refine ⟨84291137115444415075203659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56194091410296276716802439 84291137115444415075203659)
    ·
      refine ⟨126436705673166622612805489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84291137115444415075203659 126436705673166622612805489)
      ·
        refine ⟨94827529254874966959604117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126436705673166622612805489 94827529254874966959604117)
        ·
          refine ⟨4445040433822264076231443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94827529254874966959604117 4445040433822264076231443)
          ·
            refine ⟨6667560650733396114347165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445040433822264076231443 6667560650733396114347165)
            ·
              refine ⟨2500335244025023542880187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6667560650733396114347165 2500335244025023542880187)
              ·
                refine ⟨3750502866037535314320281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500335244025023542880187 3750502866037535314320281)
                ·
                  refine ⟨2812877149528151485740211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3750502866037535314320281 2812877149528151485740211)
                  ·
                    refine ⟨4219315724292227228610317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2812877149528151485740211 4219315724292227228610317)
                    ·
                      refine ⟨1582243396609585210728869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4219315724292227228610317 1582243396609585210728869)
                      ·
                        rfl

theorem cell23_3081408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_3081408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081408 prefixEnd_3081408 := by exact prefixLift 3081408
  have htrace : WordTrace (prefixWord ++ tailWord_3081408) baseStart_3081408 baseEnd_3081408 := by
    simpa [prefixWord, tailWord_3081408, baseEnd_3081408] using wordTrace_append hprefix tailTrace_3081408
  have hstable : (prefixWord ++ tailWord_3081408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081408).length < 2 ^ (prefixWord ++ tailWord_3081408).sum := by decide
  have hdescent : baseEnd_3081408 < baseStart_3081408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081454 : List Nat := [4, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_3081454 : Nat := 118140960795 + 3081454 * 2 ^ 59
def prefixEnd_3081454 : Nat := 4983230072969 + 3 ^ 40 * 3081454 * 2
def baseEnd_3081454 : Nat := 175807446302188003417073

theorem tailTrace_3081454 : CollatzResearch.WordTrace tailWord_3081454 prefixEnd_3081454 175807446302188003417073 := by
  unfold tailWord_3081454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14048732572303237911222427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74926573718950602193186277 14048732572303237911222427)
  ·
    refine ⟨21073098858454856866833641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14048732572303237911222427 21073098858454856866833641)
    ·
      refine ⟨15804824143841142650125231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21073098858454856866833641 15804824143841142650125231)
      ·
        refine ⟨23707236215761713975187847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15804824143841142650125231 23707236215761713975187847)
        ·
          refine ⟨35560854323642570962781771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23707236215761713975187847 35560854323642570962781771)
          ·
            refine ⟨53341281485463856444172657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35560854323642570962781771 53341281485463856444172657)
            ·
              refine ⟨40005961114097892333129493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53341281485463856444172657 40005961114097892333129493)
              ·
                refine ⟨1875279427223338703115445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40005961114097892333129493 1875279427223338703115445)
                ·
                  refine ⟨175807446302188003417073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1875279427223338703115445 175807446302188003417073)
                  ·
                    rfl

theorem cell23_3081454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_3081454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081454 prefixEnd_3081454 := by exact prefixLift 3081454
  have htrace : WordTrace (prefixWord ++ tailWord_3081454) baseStart_3081454 baseEnd_3081454 := by
    simpa [prefixWord, tailWord_3081454, baseEnd_3081454] using wordTrace_append hprefix tailTrace_3081454
  have hstable : (prefixWord ++ tailWord_3081454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081454).length < 2 ^ (prefixWord ++ tailWord_3081454).sum := by decide
  have hdescent : baseEnd_3081454 < baseStart_3081454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081484 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_3081484 : Nat := 118140960795 + 3081484 * 2 ^ 59
def prefixEnd_3081484 : Nat := 4983230072969 + 3 ^ 40 * 3081484 * 2
def baseEnd_3081484 : Nat := 527427473713108971126173

theorem tailTrace_3081484 : CollatzResearch.WordTrace tailWord_3081484 prefixEnd_3081484 527427473713108971126173 := by
  unfold tailWord_3081484
  simp only [CollatzResearch.WordTrace]
  refine ⟨56195477384158609206685753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74927303178878145608914337 56195477384158609206685753)
  ·
    refine ⟨42146608038118956905014315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56195477384158609206685753 42146608038118956905014315)
    ·
      refine ⟨63219912057178435357521473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42146608038118956905014315 63219912057178435357521473)
      ·
        refine ⟨47414934042883826518141105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63219912057178435357521473 47414934042883826518141105)
        ·
          refine ⟨35561200532162869888605829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47414934042883826518141105 35561200532162869888605829)
          ·
            refine ⟨6667725099780538104113593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35561200532162869888605829 6667725099780538104113593)
            ·
              refine ⟨5000793824835403578085195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667725099780538104113593 5000793824835403578085195)
              ·
                refine ⟨7501190737253105367127793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5000793824835403578085195 7501190737253105367127793)
                ·
                  refine ⟨5625893052939829025345845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7501190737253105367127793 5625893052939829025345845)
                  ·
                    refine ⟨527427473713108971126173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5625893052939829025345845 527427473713108971126173)
                    ·
                      rfl

theorem cell23_3081484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_3081484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081484 prefixEnd_3081484 := by exact prefixLift 3081484
  have htrace : WordTrace (prefixWord ++ tailWord_3081484) baseStart_3081484 baseEnd_3081484 := by
    simpa [prefixWord, tailWord_3081484, baseEnd_3081484] using wordTrace_append hprefix tailTrace_3081484
  have hstable : (prefixWord ++ tailWord_3081484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081484).length < 2 ^ (prefixWord ++ tailWord_3081484).sum := by decide
  have hdescent : baseEnd_3081484 < baseStart_3081484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081521 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 2, 4, 2]
def baseStart_3081521 : Nat := 118140960795 + 3081521 * 2 ^ 59
def prefixEnd_3081521 : Nat := 4983230072969 + 3 ^ 40 * 3081521 * 2
def baseEnd_3081521 : Nat := 1582301419923543268615849

theorem tailTrace_3081521 : CollatzResearch.WordTrace tailWord_3081521 prefixEnd_3081521 1582301419923543268615849 := by
  unfold tailWord_3081521
  simp only [CollatzResearch.WordTrace]
  refine ⟨112392304269183173732468417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74928202846122115821645611 112392304269183173732468417)
  ·
    refine ⟨84294228201887380299351313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112392304269183173732468417 84294228201887380299351313)
    ·
      refine ⟨63220671151415535224513485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84294228201887380299351313 63220671151415535224513485)
      ·
        refine ⟨23707751681780825709192557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63220671151415535224513485 23707751681780825709192557)
        ·
          refine ⟨8890406880667809640947209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23707751681780825709192557 8890406880667809640947209)
          ·
            refine ⟨6667805160500857230710407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8890406880667809640947209 6667805160500857230710407)
            ·
              refine ⟨10001707740751285846065611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667805160500857230710407 10001707740751285846065611)
              ·
                refine ⟨15002561611126928769098417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001707740751285846065611 15002561611126928769098417)
                ·
                  refine ⟨11251921208345196576823813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15002561611126928769098417 11251921208345196576823813)
                  ·
                    refine ⟨2109735226564724358154465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11251921208345196576823813 2109735226564724358154465)
                    ·
                      refine ⟨1582301419923543268615849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109735226564724358154465 1582301419923543268615849)
                      ·
                        rfl

theorem cell23_3081521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_3081521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081521 prefixEnd_3081521 := by exact prefixLift 3081521
  have htrace : WordTrace (prefixWord ++ tailWord_3081521) baseStart_3081521 baseEnd_3081521 := by
    simpa [prefixWord, tailWord_3081521, baseEnd_3081521] using wordTrace_append hprefix tailTrace_3081521
  have hstable : (prefixWord ++ tailWord_3081521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081521).length < 2 ^ (prefixWord ++ tailWord_3081521).sum := by decide
  have hdescent : baseEnd_3081521 < baseStart_3081521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081548 : List Nat := [2, 2, 1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_3081548 : Nat := 118140960795 + 3081548 * 2 ^ 59
def prefixEnd_3081548 : Nat := 4983230072969 + 3 ^ 40 * 3081548 * 2
def baseEnd_3081548 : Nat := 527438427967071554326075

theorem tailTrace_3081548 : CollatzResearch.WordTrace tailWord_3081548 prefixEnd_3081548 527438427967071554326075 := by
  unfold tailWord_3081548
  simp only [CollatzResearch.WordTrace]
  refine ⟨56196644520042678671850649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74928859360056904895800865 56196644520042678671850649)
  ·
    refine ⟨42147483390032009003887987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56196644520042678671850649 42147483390032009003887987)
    ·
      refine ⟨63221225085048013505831981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42147483390032009003887987 63221225085048013505831981)
      ·
        refine ⟨23707959406893005064686993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63221225085048013505831981 23707959406893005064686993)
        ·
          refine ⟨17780969555169753798515245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23707959406893005064686993 17780969555169753798515245)
          ·
            refine ⟨6667863583188657674443217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17780969555169753798515245 6667863583188657674443217)
            ·
              refine ⟨5000897687391493255832413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667863583188657674443217 5000897687391493255832413)
              ·
                refine ⟨1875336632771809970937155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5000897687391493255832413 1875336632771809970937155)
                ·
                  refine ⟨2813004949157714956405733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875336632771809970937155 2813004949157714956405733)
                  ·
                    refine ⟨527438427967071554326075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813004949157714956405733 527438427967071554326075)
                    ·
                      rfl

theorem cell23_3081548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_3081548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081548 prefixEnd_3081548 := by exact prefixLift 3081548
  have htrace : WordTrace (prefixWord ++ tailWord_3081548) baseStart_3081548 baseEnd_3081548 := by
    simpa [prefixWord, tailWord_3081548, baseEnd_3081548] using wordTrace_append hprefix tailTrace_3081548
  have hstable : (prefixWord ++ tailWord_3081548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081548).length < 2 ^ (prefixWord ++ tailWord_3081548).sum := by decide
  have hdescent : baseEnd_3081548 < baseStart_3081548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081571 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 3]
def baseStart_3081571 : Nat := 118140960795 + 3081571 * 2 ^ 59
def prefixEnd_3081571 : Nat := 4983230072969 + 3 ^ 40 * 3081571 * 2
def baseEnd_3081571 : Nat := 1582327093956268072990619

theorem tailTrace_3081571 : CollatzResearch.WordTrace tailWord_3081571 prefixEnd_3081571 1582327093956268072990619 := by
  unfold tailWord_3081571
  simp only [CollatzResearch.WordTrace]
  refine ⟨112394127919002032271788567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74929418612668021514525711 112394127919002032271788567)
  ·
    refine ⟨168591191878503048407682851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112394127919002032271788567 168591191878503048407682851)
    ·
      refine ⟨252886787817754572611524277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168591191878503048407682851 252886787817754572611524277)
      ·
        refine ⟨23708136357914491182330401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 252886787817754572611524277 23708136357914491182330401)
        ·
          refine ⟨17781102268435868386747801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23708136357914491182330401 17781102268435868386747801)
          ·
            refine ⟨13335826701326901290060851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17781102268435868386747801 13335826701326901290060851)
            ·
              refine ⟨20003740051990351935091277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13335826701326901290060851 20003740051990351935091277)
              ·
                refine ⟨7501402519496381975659229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20003740051990351935091277 7501402519496381975659229)
                ·
                  refine ⟨2813025944811143240872211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7501402519496381975659229 2813025944811143240872211)
                  ·
                    refine ⟨4219538917216714861308317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2813025944811143240872211 4219538917216714861308317)
                    ·
                      refine ⟨1582327093956268072990619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4219538917216714861308317 1582327093956268072990619)
                      ·
                        rfl

theorem cell23_3081571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_3081571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081571 prefixEnd_3081571 := by exact prefixLift 3081571
  have htrace : WordTrace (prefixWord ++ tailWord_3081571) baseStart_3081571 baseEnd_3081571 := by
    simpa [prefixWord, tailWord_3081571, baseEnd_3081571] using wordTrace_append hprefix tailTrace_3081571
  have hstable : (prefixWord ++ tailWord_3081571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081571).length < 2 ^ (prefixWord ++ tailWord_3081571).sum := by decide
  have hdescent : baseEnd_3081571 < baseStart_3081571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081577 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_3081577 : Nat := 118140960795 + 3081577 * 2 ^ 59
def prefixEnd_3081577 : Nat := 4983230072969 + 3 ^ 40 * 3081577 * 2
def baseEnd_3081577 : Nat := 1582330174840195049515591

theorem tailTrace_3081577 : CollatzResearch.WordTrace tailWord_3081577 prefixEnd_3081577 1582330174840195049515591 := by
  unfold tailWord_3081577
  simp only [CollatzResearch.WordTrace]
  refine ⟨112394346756980295296506985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74929564504653530197671323 112394346756980295296506985)
  ·
    refine ⟨84295760067735221472380239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112394346756980295296506985 84295760067735221472380239)
    ·
      refine ⟨126443640101602832208570359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84295760067735221472380239 126443640101602832208570359)
      ·
        refine ⟨189665460152404248312855539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126443640101602832208570359 189665460152404248312855539)
        ·
          refine ⟨284498190228606372469283309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189665460152404248312855539 284498190228606372469283309)
          ·
            refine ⟨106686821335727389675981241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284498190228606372469283309 106686821335727389675981241)
            ·
              refine ⟨80015116001795542256985931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106686821335727389675981241 80015116001795542256985931)
              ·
                refine ⟨120022674002693313385478897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80015116001795542256985931 120022674002693313385478897)
                ·
                  refine ⟨90017005502019985039109173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120022674002693313385478897 90017005502019985039109173)
                  ·
                    refine ⟨8439094265814373597416485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90017005502019985039109173 8439094265814373597416485)
                    ·
                      refine ⟨1582330174840195049515591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8439094265814373597416485 1582330174840195049515591)
                      ·
                        rfl

theorem cell23_3081577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_3081577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081577 prefixEnd_3081577 := by exact prefixLift 3081577
  have htrace : WordTrace (prefixWord ++ tailWord_3081577) baseStart_3081577 baseEnd_3081577 := by
    simpa [prefixWord, tailWord_3081577, baseEnd_3081577] using wordTrace_append hprefix tailTrace_3081577
  have hstable : (prefixWord ++ tailWord_3081577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081577).length < 2 ^ (prefixWord ++ tailWord_3081577).sum := by decide
  have hdescent : baseEnd_3081577 < baseStart_3081577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081578 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 6]
def baseStart_3081578 : Nat := 118140960795 + 3081578 * 2 ^ 59
def prefixEnd_3081578 : Nat := 4983230072969 + 3 ^ 40 * 3081578 * 2
def baseEnd_3081578 : Nat := 175814520924538838400343

theorem tailTrace_3081578 : CollatzResearch.WordTrace tailWord_3081578 prefixEnd_3081578 175814520924538838400343 := by
  unfold tailWord_3081578
  simp only [CollatzResearch.WordTrace]
  refine ⟨28098595807494168116823347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74929588819984448311528925 28098595807494168116823347)
  ·
    refine ⟨42147893711241252175235021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28098595807494168116823347 42147893711241252175235021)
    ·
      refine ⟨15805460141715469565713133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42147893711241252175235021 15805460141715469565713133)
      ·
        refine ⟨5927047553143301087142425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15805460141715469565713133 5927047553143301087142425)
        ·
          refine ⟨4445285664857475815356819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5927047553143301087142425 4445285664857475815356819)
          ·
            refine ⟨6667928497286213723035229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445285664857475815356819 6667928497286213723035229)
            ·
              refine ⟨2500473186482330146138211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6667928497286213723035229 2500473186482330146138211)
              ·
                refine ⟨3750709779723495219207317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500473186482330146138211 3750709779723495219207317)
                ·
                  refine ⟨175814520924538838400343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3750709779723495219207317 175814520924538838400343)
                  ·
                    rfl

theorem cell23_3081578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_3081578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081578 prefixEnd_3081578 := by exact prefixLift 3081578
  have htrace : WordTrace (prefixWord ++ tailWord_3081578) baseStart_3081578 baseEnd_3081578 := by
    simpa [prefixWord, tailWord_3081578, baseEnd_3081578] using wordTrace_append hprefix tailTrace_3081578
  have hstable : (prefixWord ++ tailWord_3081578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081578).length < 2 ^ (prefixWord ++ tailWord_3081578).sum := by decide
  have hdescent : baseEnd_3081578 < baseStart_3081578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081581 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_3081581 : Nat := 118140960795 + 3081581 * 2 ^ 59
def prefixEnd_3081581 : Nat := 4983230072969 + 3 ^ 40 * 3081581 * 2
def baseEnd_3081581 : Nat := 1582332228762813033865573

theorem tailTrace_3081581 : CollatzResearch.WordTrace tailWord_3081581 prefixEnd_3081581 1582332228762813033865573 := by
  unfold tailWord_3081581
  simp only [CollatzResearch.WordTrace]
  refine ⟨112394492648965803979652597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74929661765977202653101731 112394492648965803979652597)
  ·
    refine ⟨10536983685840544123092431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112394492648965803979652597 10536983685840544123092431)
    ·
      refine ⟨15805475528760816184638647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10536983685840544123092431 15805475528760816184638647)
      ·
        refine ⟨23708213293141224276957971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15805475528760816184638647 23708213293141224276957971)
        ·
          refine ⟨35562319939711836415436957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23708213293141224276957971 35562319939711836415436957)
          ·
            refine ⟨13335869977391938655788859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35562319939711836415436957 13335869977391938655788859)
            ·
              refine ⟨20003804966087907983683289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13335869977391938655788859 20003804966087907983683289)
              ·
                refine ⟨15002853724565930987762467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20003804966087907983683289 15002853724565930987762467)
                ·
                  refine ⟨22504280586848896481643701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15002853724565930987762467 22504280586848896481643701)
                  ·
                    refine ⟨2109776305017084045154097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22504280586848896481643701 2109776305017084045154097)
                    ·
                      refine ⟨1582332228762813033865573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109776305017084045154097 1582332228762813033865573)
                      ·
                        rfl

theorem cell23_3081581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_3081581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081581 prefixEnd_3081581 := by exact prefixLift 3081581
  have htrace : WordTrace (prefixWord ++ tailWord_3081581) baseStart_3081581 baseEnd_3081581 := by
    simpa [prefixWord, tailWord_3081581, baseEnd_3081581] using wordTrace_append hprefix tailTrace_3081581
  have hstable : (prefixWord ++ tailWord_3081581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081581).length < 2 ^ (prefixWord ++ tailWord_3081581).sum := by decide
  have hdescent : baseEnd_3081581 < baseStart_3081581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081634 : List Nat := [3, 3, 1, 2, 1, 2, 1, 10]
def baseStart_3081634 : Nat := 118140960795 + 3081634 * 2 ^ 59
def prefixEnd_3081634 : Nat := 4983230072969 + 3 ^ 40 * 3081634 * 2
def baseEnd_3081634 : Nat := 58605905305092641722327

theorem tailTrace_3081634 : CollatzResearch.WordTrace tailWord_3081634 prefixEnd_3081634 58605905305092641722327 := by
  unfold tailWord_3081634
  simp only [CollatzResearch.WordTrace]
  refine ⟨28099106429443448507832989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74930950478515862687554637 28099106429443448507832989)
  ·
    refine ⟨10537164911041293190437371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28099106429443448507832989 10537164911041293190437371)
    ·
      refine ⟨15805747366561939785656057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10537164911041293190437371 15805747366561939785656057)
      ·
        refine ⟨11854310524921454839242043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15805747366561939785656057 11854310524921454839242043)
        ·
          refine ⟨17781465787382182258863065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11854310524921454839242043 17781465787382182258863065)
          ·
            refine ⟨13336099340536636694147299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17781465787382182258863065 13336099340536636694147299)
            ·
              refine ⟨20004149010804955041220949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13336099340536636694147299 20004149010804955041220949)
              ·
                refine ⟨58605905305092641722327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20004149010804955041220949 58605905305092641722327)
                ·
                  rfl

theorem cell23_3081634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 10].length) (baseStart_3081634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081634 prefixEnd_3081634 := by exact prefixLift 3081634
  have htrace : WordTrace (prefixWord ++ tailWord_3081634) baseStart_3081634 baseEnd_3081634 := by
    simpa [prefixWord, tailWord_3081634, baseEnd_3081634] using wordTrace_append hprefix tailTrace_3081634
  have hstable : (prefixWord ++ tailWord_3081634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081634).length < 2 ^ (prefixWord ++ tailWord_3081634).sum := by decide
  have hdescent : baseEnd_3081634 < baseStart_3081634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081645 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3081645 : Nat := 118140960795 + 3081645 * 2 ^ 59
def prefixEnd_3081645 : Nat := 4983230072969 + 3 ^ 40 * 3081645 * 2
def baseEnd_3081645 : Nat := 1582365091524700783465279

theorem tailTrace_3081645 : CollatzResearch.WordTrace tailWord_3081645 prefixEnd_3081645 1582365091524700783465279 := by
  unfold tailWord_3081645
  simp only [CollatzResearch.WordTrace]
  refine ⟨112396826920733942909982389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74931217947155961939988259 112396826920733942909982389)
  ·
    refine ⟨10537202523818807147810849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112396826920733942909982389 10537202523818807147810849)
    ·
      refine ⟨7902901892864105360858137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10537202523818807147810849 7902901892864105360858137)
      ·
        refine ⟨5927176419648079020643603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7902901892864105360858137 5927176419648079020643603)
        ·
          refine ⟨8890764629472118530965405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5927176419648079020643603 8890764629472118530965405)
          ·
            refine ⟨3334036736052044449112027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8890764629472118530965405 3334036736052044449112027)
            ·
              refine ⟨5001055104078066673668041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334036736052044449112027 5001055104078066673668041)
              ·
                refine ⟨3750791328058550005251031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5001055104078066673668041 3750791328058550005251031)
                ·
                  refine ⟨5626186992087825007876547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750791328058550005251031 5626186992087825007876547)
                  ·
                    refine ⟨8439280488131737511814821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5626186992087825007876547 8439280488131737511814821)
                    ·
                      refine ⟨1582365091524700783465279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8439280488131737511814821 1582365091524700783465279)
                      ·
                        rfl

theorem cell23_3081645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3081645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081645 prefixEnd_3081645 := by exact prefixLift 3081645
  have htrace : WordTrace (prefixWord ++ tailWord_3081645) baseStart_3081645 baseEnd_3081645 := by
    simpa [prefixWord, tailWord_3081645, baseEnd_3081645] using wordTrace_append hprefix tailTrace_3081645
  have hstable : (prefixWord ++ tailWord_3081645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081645).length < 2 ^ (prefixWord ++ tailWord_3081645).sum := by decide
  have hdescent : baseEnd_3081645 < baseStart_3081645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081661 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_3081661 : Nat := 118140960795 + 3081661 * 2 ^ 59
def prefixEnd_3081661 : Nat := 4983230072969 + 3 ^ 40 * 3081661 * 2
def baseEnd_3081661 : Nat := 1582373307215172720865205

theorem tailTrace_3081661 : CollatzResearch.WordTrace tailWord_3081661 prefixEnd_3081661 1582373307215172720865205 := by
  unfold tailWord_3081661
  simp only [CollatzResearch.WordTrace]
  refine ⟨112397410488675977642564837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74931606992450651761709891 112397410488675977642564837)
  ·
    refine ⟨21074514466626745807980907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112397410488675977642564837 21074514466626745807980907)
    ·
      refine ⟨31611771699940118711971361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21074514466626745807980907 31611771699940118711971361)
      ·
        refine ⟨23708828774955089033978521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31611771699940118711971361 23708828774955089033978521)
        ·
          refine ⟨17781621581216316775483891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23708828774955089033978521 17781621581216316775483891)
          ·
            refine ⟨26672432371824475163225837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17781621581216316775483891 26672432371824475163225837)
            ·
              refine ⟨10002162139434178186209689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26672432371824475163225837 10002162139434178186209689)
              ·
                refine ⟨7501621604575633639657267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10002162139434178186209689 7501621604575633639657267)
                ·
                  refine ⟨11252432406863450459485901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7501621604575633639657267 11252432406863450459485901)
                  ·
                    refine ⟨4219662152573793922307213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11252432406863450459485901 4219662152573793922307213)
                    ·
                      refine ⟨1582373307215172720865205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4219662152573793922307213 1582373307215172720865205)
                      ·
                        rfl

theorem cell23_3081661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_3081661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081661 prefixEnd_3081661 := by exact prefixLift 3081661
  have htrace : WordTrace (prefixWord ++ tailWord_3081661) baseStart_3081661 baseEnd_3081661 := by
    simpa [prefixWord, tailWord_3081661, baseEnd_3081661] using wordTrace_append hprefix tailTrace_3081661
  have hstable : (prefixWord ++ tailWord_3081661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081661).length < 2 ^ (prefixWord ++ tailWord_3081661).sum := by decide
  have hdescent : baseEnd_3081661 < baseStart_3081661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081678 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_3081678 : Nat := 118140960795 + 3081678 * 2 ^ 59
def prefixEnd_3081678 : Nat := 4983230072969 + 3 ^ 40 * 3081678 * 2
def baseEnd_3081678 : Nat := 1582382036386299154352627

theorem tailTrace_3081678 : CollatzResearch.WordTrace tailWord_3081678 prefixEnd_3081678 1582382036386299154352627 := by
  unfold tailWord_3081678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14049753816201798693241711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74932020353076259697289125 14049753816201798693241711)
  ·
    refine ⟨21074630724302698039862567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14049753816201798693241711 21074630724302698039862567)
    ·
      refine ⟨31611946086454047059793851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21074630724302698039862567 31611946086454047059793851)
      ·
        refine ⟨47417919129681070589690777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31611946086454047059793851 47417919129681070589690777)
        ·
          refine ⟨35563439347260802942268083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47417919129681070589690777 35563439347260802942268083)
          ·
            refine ⟨53345159020891204413402125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35563439347260802942268083 53345159020891204413402125)
            ·
              refine ⟨20004434632834201655025797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53345159020891204413402125 20004434632834201655025797)
              ·
                refine ⟨3750831493656412810317337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20004434632834201655025797 3750831493656412810317337)
                ·
                  refine ⟨2813123620242309607738003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3750831493656412810317337 2813123620242309607738003)
                  ·
                    refine ⟨4219685430363464411607005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2813123620242309607738003 4219685430363464411607005)
                    ·
                      refine ⟨1582382036386299154352627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4219685430363464411607005 1582382036386299154352627)
                      ·
                        rfl

theorem cell23_3081678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_3081678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081678 prefixEnd_3081678 := by exact prefixLift 3081678
  have htrace : WordTrace (prefixWord ++ tailWord_3081678) baseStart_3081678 baseEnd_3081678 := by
    simpa [prefixWord, tailWord_3081678, baseEnd_3081678] using wordTrace_append hprefix tailTrace_3081678
  have hstable : (prefixWord ++ tailWord_3081678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081678).length < 2 ^ (prefixWord ++ tailWord_3081678).sum := by decide
  have hdescent : baseEnd_3081678 < baseStart_3081678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081735 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_3081735 : Nat := 118140960795 + 3081735 * 2 ^ 59
def prefixEnd_3081735 : Nat := 4983230072969 + 3 ^ 40 * 3081735 * 2
def baseEnd_3081735 : Nat := 1582411304783605431339865

theorem tailTrace_3081735 : CollatzResearch.WordTrace tailWord_3081735 prefixEnd_3081735 1582411304783605431339865 := by
  unfold tailWord_3081735
  simp only [CollatzResearch.WordTrace]
  refine ⟨112400109490407888280758659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74933406326938592187172439 112400109490407888280758659)
  ·
    refine ⟨168600164235611832421137989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112400109490407888280758659 168600164235611832421137989)
    ·
      refine ⟨31612530794177218578963373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168600164235611832421137989 31612530794177218578963373)
      ·
        refine ⟨11854699047816456967111265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31612530794177218578963373 11854699047816456967111265)
        ·
          refine ⟨8891024285862342725333449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11854699047816456967111265 8891024285862342725333449)
          ·
            refine ⟨6668268214396757044000087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8891024285862342725333449 6668268214396757044000087)
            ·
              refine ⟨10002402321595135566000131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668268214396757044000087 10002402321595135566000131)
              ·
                refine ⟨15003603482392703349000197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10002402321595135566000131 15003603482392703349000197)
                ·
                  refine ⟨2813175652948631877937537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15003603482392703349000197 2813175652948631877937537)
                  ·
                    refine ⟨2109881739711473908453153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2813175652948631877937537 2109881739711473908453153)
                    ·
                      refine ⟨1582411304783605431339865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109881739711473908453153 1582411304783605431339865)
                      ·
                        rfl

theorem cell23_3081735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_3081735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081735 prefixEnd_3081735 := by exact prefixLift 3081735
  have htrace : WordTrace (prefixWord ++ tailWord_3081735) baseStart_3081735 baseEnd_3081735 := by
    simpa [prefixWord, tailWord_3081735, baseEnd_3081735] using wordTrace_append hprefix tailTrace_3081735
  have hstable : (prefixWord ++ tailWord_3081735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081735).length < 2 ^ (prefixWord ++ tailWord_3081735).sum := by decide
  have hdescent : baseEnd_3081735 < baseStart_3081735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081752 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 1, 4, 2]
def baseStart_3081752 : Nat := 118140960795 + 3081752 * 2 ^ 59
def prefixEnd_3081752 : Nat := 4983230072969 + 3 ^ 40 * 3081752 * 2
def baseEnd_3081752 : Nat := 1582420033954731864827287

theorem tailTrace_3081752 : CollatzResearch.WordTrace tailWord_3081752 prefixEnd_3081752 1582420033954731864827287 := by
  unfold tailWord_3081752
  simp only [CollatzResearch.WordTrace]
  refine ⟨56200364765673150092063755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74933819687564200122751673 56200364765673150092063755)
  ·
    refine ⟨84300547148509725138095633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56200364765673150092063755 84300547148509725138095633)
    ·
      refine ⟨63225410361382293853571725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84300547148509725138095633 63225410361382293853571725)
      ·
        refine ⟨23709528885518360195089397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63225410361382293853571725 23709528885518360195089397)
        ·
          refine ⟨2222768333017346268289631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23709528885518360195089397 2222768333017346268289631)
          ·
            refine ⟨3334152499526019402434447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222768333017346268289631 3334152499526019402434447)
            ·
              refine ⟨5001228749289029103651671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334152499526019402434447 5001228749289029103651671)
              ·
                refine ⟨7501843123933543655477507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001228749289029103651671 7501843123933543655477507)
                ·
                  refine ⟨11252764685900315483216261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7501843123933543655477507 11252764685900315483216261)
                  ·
                    refine ⟨2109893378606309153103049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11252764685900315483216261 2109893378606309153103049)
                    ·
                      refine ⟨1582420033954731864827287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109893378606309153103049 1582420033954731864827287)
                      ·
                        rfl

theorem cell23_3081752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_3081752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081752 prefixEnd_3081752 := by exact prefixLift 3081752
  have htrace : WordTrace (prefixWord ++ tailWord_3081752) baseStart_3081752 baseEnd_3081752 := by
    simpa [prefixWord, tailWord_3081752, baseEnd_3081752] using wordTrace_append hprefix tailTrace_3081752
  have hstable : (prefixWord ++ tailWord_3081752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081752).length < 2 ^ (prefixWord ++ tailWord_3081752).sum := by decide
  have hdescent : baseEnd_3081752 < baseStart_3081752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081788 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_3081788 : Nat := 118140960795 + 3081788 * 2 ^ 59
def prefixEnd_3081788 : Nat := 4983230072969 + 3 ^ 40 * 3081788 * 2
def baseEnd_3081788 : Nat := 527479506419431241325707

theorem tailTrace_3081788 : CollatzResearch.WordTrace tailWord_3081788 prefixEnd_3081788 527479506419431241325707 := by
  unfold tailWord_3081788
  simp only [CollatzResearch.WordTrace]
  refine ⟨56201021279607939166219009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74934695039477252221625345 56201021279607939166219009)
  ·
    refine ⟨42150765959705954374664257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56201021279607939166219009 42150765959705954374664257)
    ·
      refine ⟨31613074469779465780998193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42150765959705954374664257 31613074469779465780998193)
      ·
        refine ⟨23709805852334599335748645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31613074469779465780998193 23709805852334599335748645)
        ·
          refine ⟨4445588597312737375452871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23709805852334599335748645 4445588597312737375452871)
          ·
            refine ⟨6668382895969106063179307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445588597312737375452871 6668382895969106063179307)
            ·
              refine ⟨10002574343953659094768961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668382895969106063179307 10002574343953659094768961)
              ·
                refine ⟨7501930757965244321076721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10002574343953659094768961 7501930757965244321076721)
                ·
                  refine ⟨5626448068473933240807541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7501930757965244321076721 5626448068473933240807541)
                  ·
                    refine ⟨527479506419431241325707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5626448068473933240807541 527479506419431241325707)
                    ·
                      rfl

theorem cell23_3081788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_3081788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081788 prefixEnd_3081788 := by exact prefixLift 3081788
  have htrace : WordTrace (prefixWord ++ tailWord_3081788) baseStart_3081788 baseEnd_3081788 := by
    simpa [prefixWord, tailWord_3081788, baseEnd_3081788] using wordTrace_append hprefix tailTrace_3081788
  have hstable : (prefixWord ++ tailWord_3081788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081788).length < 2 ^ (prefixWord ++ tailWord_3081788).sum := by decide
  have hdescent : baseEnd_3081788 < baseStart_3081788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081791 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_3081791 : Nat := 118140960795 + 3081791 * 2 ^ 59
def prefixEnd_3081791 : Nat := 4983230072969 + 3 ^ 40 * 3081791 * 2
def baseEnd_3081791 : Nat := 1582440059700257212239607

theorem tailTrace_3081791 : CollatzResearch.WordTrace tailWord_3081791 prefixEnd_3081791 1582440059700257212239607 := by
  unfold tailWord_3081791
  simp only [CollatzResearch.WordTrace]
  refine ⟨112402151978205009844797227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74934767985470006563198151 112402151978205009844797227)
  ·
    refine ⟨168603227967307514767195841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112402151978205009844797227 168603227967307514767195841)
    ·
      refine ⟨126452420975480636075396881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168603227967307514767195841 126452420975480636075396881)
      ·
        refine ⟨94839315731610477056547661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126452420975480636075396881 94839315731610477056547661)
        ·
          refine ⟨35564743399353928896205373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94839315731610477056547661 35564743399353928896205373)
          ·
            refine ⟨13336778774757723336077015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35564743399353928896205373 13336778774757723336077015)
            ·
              refine ⟨20005168162136585004115523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13336778774757723336077015 20005168162136585004115523)
              ·
                refine ⟨30007752243204877506173285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20005168162136585004115523 30007752243204877506173285)
                ·
                  refine ⟨5626453545600914532407491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30007752243204877506173285 5626453545600914532407491)
                  ·
                    refine ⟨8439680318401371798611237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5626453545600914532407491 8439680318401371798611237)
                    ·
                      refine ⟨1582440059700257212239607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8439680318401371798611237 1582440059700257212239607)
                      ·
                        rfl

theorem cell23_3081791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_3081791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081791 prefixEnd_3081791 := by exact prefixLift 3081791
  have htrace : WordTrace (prefixWord ++ tailWord_3081791) baseStart_3081791 baseEnd_3081791 := by
    simpa [prefixWord, tailWord_3081791, baseEnd_3081791] using wordTrace_append hprefix tailTrace_3081791
  have hstable : (prefixWord ++ tailWord_3081791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081791).length < 2 ^ (prefixWord ++ tailWord_3081791).sum := by decide
  have hdescent : baseEnd_3081791 < baseStart_3081791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081828 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_3081828 : Nat := 118140960795 + 3081828 * 2 ^ 59
def prefixEnd_3081828 : Nat := 4983230072969 + 3 ^ 40 * 3081828 * 2
def baseEnd_3081828 : Nat := 1582459058484473567476937

theorem tailTrace_3081828 : CollatzResearch.WordTrace tailWord_3081828 prefixEnd_3081828 1582459058484473567476937 := by
  unfold tailWord_3081828
  simp only [CollatzResearch.WordTrace]
  refine ⟨56201750739535482581947069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74935667652713976775929425 56201750739535482581947069)
  ·
    refine ⟨21075656527325805968230151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56201750739535482581947069 21075656527325805968230151)
    ·
      refine ⟨31613484790988708952345227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21075656527325805968230151 31613484790988708952345227)
      ·
        refine ⟨47420227186483063428517841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31613484790988708952345227 47420227186483063428517841)
        ·
          refine ⟨35565170389862297571388381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47420227186483063428517841 35565170389862297571388381)
          ·
            refine ⟨13336938896198361589270643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35565170389862297571388381 13336938896198361589270643)
            ·
              refine ⟨20005408344297542383905965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13336938896198361589270643 20005408344297542383905965)
              ·
                refine ⟨7502028129111578393964737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20005408344297542383905965 7502028129111578393964737)
                ·
                  refine ⟨5626521096833683795473553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7502028129111578393964737 5626521096833683795473553)
                  ·
                    refine ⟨4219890822625262846605165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5626521096833683795473553 4219890822625262846605165)
                    ·
                      refine ⟨1582459058484473567476937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4219890822625262846605165 1582459058484473567476937)
                      ·
                        rfl

theorem cell23_3081828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_3081828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081828 prefixEnd_3081828 := by exact prefixLift 3081828
  have htrace : WordTrace (prefixWord ++ tailWord_3081828) baseStart_3081828 baseEnd_3081828 := by
    simpa [prefixWord, tailWord_3081828, baseEnd_3081828] using wordTrace_append hprefix tailTrace_3081828
  have hstable : (prefixWord ++ tailWord_3081828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081828).length < 2 ^ (prefixWord ++ tailWord_3081828).sum := by decide
  have hdescent : baseEnd_3081828 < baseStart_3081828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081845 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3081845 : Nat := 118140960795 + 3081845 * 2 ^ 59
def prefixEnd_3081845 : Nat := 4983230072969 + 3 ^ 40 * 3081845 * 2
def baseEnd_3081845 : Nat := 1582467787655600000964359

theorem tailTrace_3081845 : CollatzResearch.WordTrace tailWord_3081845 prefixEnd_3081845 1582467787655600000964359 := by
  unfold tailWord_3081845
  simp only [CollatzResearch.WordTrace]
  refine ⟨112404121520009377067262989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74936081013339584711508659 112404121520009377067262989)
  ·
    refine ⟨42151545570003516400223621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112404121520009377067262989 42151545570003516400223621)
    ·
      refine ⟨7903414794375659325041929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42151545570003516400223621 7903414794375659325041929)
      ·
        refine ⟨5927561095781744493781447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7903414794375659325041929 5927561095781744493781447)
        ·
          refine ⟨8891341643672616740672171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5927561095781744493781447 8891341643672616740672171)
          ·
            refine ⟨13337012465508925111008257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8891341643672616740672171 13337012465508925111008257)
            ·
              refine ⟨10002759349131693833256193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13337012465508925111008257 10002759349131693833256193)
              ·
                refine ⟨7502069511848770374942145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10002759349131693833256193 7502069511848770374942145)
                ·
                  refine ⟨5626552133886577781206609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7502069511848770374942145 5626552133886577781206609)
                  ·
                    refine ⟨4219914100414933335904957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5626552133886577781206609 4219914100414933335904957)
                    ·
                      refine ⟨1582467787655600000964359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4219914100414933335904957 1582467787655600000964359)
                      ·
                        rfl

theorem cell23_3081845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3081845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081845 prefixEnd_3081845 := by exact prefixLift 3081845
  have htrace : WordTrace (prefixWord ++ tailWord_3081845) baseStart_3081845 baseEnd_3081845 := by
    simpa [prefixWord, tailWord_3081845, baseEnd_3081845] using wordTrace_append hprefix tailTrace_3081845
  have hstable : (prefixWord ++ tailWord_3081845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081845).length < 2 ^ (prefixWord ++ tailWord_3081845).sum := by decide
  have hdescent : baseEnd_3081845 < baseStart_3081845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081861 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_3081861 : Nat := 118140960795 + 3081861 * 2 ^ 59
def prefixEnd_3081861 : Nat := 4983230072969 + 3 ^ 40 * 3081861 * 2
def baseEnd_3081861 : Nat := 527492001115357312788095

theorem tailTrace_3081861 : CollatzResearch.WordTrace tailWord_3081861 prefixEnd_3081861 527492001115357312788095 := by
  unfold tailWord_3081861
  simp only [CollatzResearch.WordTrace]
  refine ⟨112404705087951411799845437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74936470058634274533230291 112404705087951411799845437)
  ·
    refine ⟨42151764407981779424942039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112404705087951411799845437 42151764407981779424942039)
    ·
      refine ⟨63227646611972669137413059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42151764407981779424942039 63227646611972669137413059)
      ·
        refine ⟨94841469917959003706119589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63227646611972669137413059 94841469917959003706119589)
        ·
          refine ⟨17782775609617313194897423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94841469917959003706119589 17782775609617313194897423)
          ·
            refine ⟨26674163414425969792346135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17782775609617313194897423 26674163414425969792346135)
            ·
              refine ⟨40011245121638954688519203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26674163414425969792346135 40011245121638954688519203)
              ·
                refine ⟨60016867682458432032778805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40011245121638954688519203 60016867682458432032778805)
                ·
                  refine ⟨5626581345230478003073013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60016867682458432032778805 5626581345230478003073013)
                  ·
                    refine ⟨527492001115357312788095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5626581345230478003073013 527492001115357312788095)
                    ·
                      rfl

theorem cell23_3081861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_3081861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081861 prefixEnd_3081861 := by exact prefixLift 3081861
  have htrace : WordTrace (prefixWord ++ tailWord_3081861) baseStart_3081861 baseEnd_3081861 := by
    simpa [prefixWord, tailWord_3081861, baseEnd_3081861] using wordTrace_append hprefix tailTrace_3081861
  have hstable : (prefixWord ++ tailWord_3081861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081861).length < 2 ^ (prefixWord ++ tailWord_3081861).sum := by decide
  have hdescent : baseEnd_3081861 < baseStart_3081861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081868 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 1, 5, 2]
def baseStart_3081868 : Nat := 118140960795 + 3081868 * 2 ^ 59
def prefixEnd_3081868 : Nat := 4983230072969 + 3 ^ 40 * 3081868 * 2
def baseEnd_3081868 : Nat := 1582479597710653410976753

theorem tailTrace_3081868 : CollatzResearch.WordTrace tailWord_3081868 prefixEnd_3081868 1582479597710653410976753 := by
  unfold tailWord_3081868
  simp only [CollatzResearch.WordTrace]
  refine ⟨56202480199463025997675129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74936640265950701330233505 56202480199463025997675129)
  ·
    refine ⟨42151860149597269498256347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56202480199463025997675129 42151860149597269498256347)
    ·
      refine ⟨63227790224395904247384521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42151860149597269498256347 63227790224395904247384521)
      ·
        refine ⟨47420842668296928185538391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63227790224395904247384521 47420842668296928185538391)
        ·
          refine ⟨71131264002445392278307587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47420842668296928185538391 71131264002445392278307587)
          ·
            refine ⟨106696896003668088417461381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71131264002445392278307587 106696896003668088417461381)
            ·
              refine ⟨20005668000687766578274009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106696896003668088417461381 20005668000687766578274009)
              ·
                refine ⟨15004251000515824933705507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20005668000687766578274009 15004251000515824933705507)
                ·
                  refine ⟨22506376500773737400558261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15004251000515824933705507 22506376500773737400558261)
                  ·
                    refine ⟨2109972796947537881302337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22506376500773737400558261 2109972796947537881302337)
                    ·
                      refine ⟨1582479597710653410976753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2109972796947537881302337 1582479597710653410976753)
                      ·
                        rfl

theorem cell23_3081868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_3081868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081868 prefixEnd_3081868 := by exact prefixLift 3081868
  have htrace : WordTrace (prefixWord ++ tailWord_3081868) baseStart_3081868 baseEnd_3081868 := by
    simpa [prefixWord, tailWord_3081868, baseEnd_3081868] using wordTrace_append hprefix tailTrace_3081868
  have hstable : (prefixWord ++ tailWord_3081868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081868).length < 2 ^ (prefixWord ++ tailWord_3081868).sum := by decide
  have hdescent : baseEnd_3081868 < baseStart_3081868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081891 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 1, 6]
def baseStart_3081891 : Nat := 118140960795 + 3081891 * 2 ^ 59
def prefixEnd_3081891 : Nat := 4983230072969 + 3 ^ 40 * 3081891 * 2
def baseEnd_3081891 : Nat := 527497135921902273663049

theorem tailTrace_3081891 : CollatzResearch.WordTrace tailWord_3081891 prefixEnd_3081891 527497135921902273663049 := by
  unfold tailWord_3081891
  simp only [CollatzResearch.WordTrace]
  refine ⟨112405799277842726923437527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74937199518561817948958351 112405799277842726923437527)
  ·
    refine ⟨168608698916764090385156291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112405799277842726923437527 168608698916764090385156291)
    ·
      refine ⟨252913048375146135577734437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168608698916764090385156291 252913048375146135577734437)
      ·
        refine ⟨47421196570339900420825207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252913048375146135577734437 47421196570339900420825207)
        ·
          refine ⟨71131794855509850631237811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47421196570339900420825207 71131794855509850631237811)
          ·
            refine ⟨106697692283264775946856717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71131794855509850631237811 106697692283264775946856717)
            ·
              refine ⟨40011634606224290980071269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106697692283264775946856717 40011634606224290980071269)
              ·
                refine ⟨7502181488667054558763363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40011634606224290980071269 7502181488667054558763363)
                ·
                  refine ⟨11253272233000581838145045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7502181488667054558763363 11253272233000581838145045)
                  ·
                    refine ⟨527497135921902273663049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11253272233000581838145045 527497135921902273663049)
                    ·
                      rfl

theorem cell23_3081891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 6].length) (baseStart_3081891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081891 prefixEnd_3081891 := by exact prefixLift 3081891
  have htrace : WordTrace (prefixWord ++ tailWord_3081891) baseStart_3081891 baseEnd_3081891 := by
    simpa [prefixWord, tailWord_3081891, baseEnd_3081891] using wordTrace_append hprefix tailTrace_3081891
  have hstable : (prefixWord ++ tailWord_3081891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081891).length < 2 ^ (prefixWord ++ tailWord_3081891).sum := by decide
  have hdescent : baseEnd_3081891 < baseStart_3081891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081892 : List Nat := [2, 3, 1, 2, 2, 2, 1, 5, 1, 1, 3]
def baseStart_3081892 : Nat := 118140960795 + 3081892 * 2 ^ 59
def prefixEnd_3081892 : Nat := 4983230072969 + 3 ^ 40 * 3081892 * 2
def baseEnd_3081892 : Nat := 1582491921246361317076643

theorem tailTrace_3081892 : CollatzResearch.WordTrace tailWord_3081892 prefixEnd_3081892 1582491921246361317076643 := by
  unfold tailWord_3081892
  simp only [CollatzResearch.WordTrace]
  refine ⟨56202917875419552047111965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74937223833892736062815953 56202917875419552047111965)
  ·
    refine ⟨21076094203282332017666987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56202917875419552047111965 21076094203282332017666987)
    ·
      refine ⟨31614141304923498026500481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21076094203282332017666987 31614141304923498026500481)
      ·
        refine ⟨23710605978692623519875361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31614141304923498026500481 23710605978692623519875361)
        ·
          refine ⟨17782954484019467639906521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23710605978692623519875361 17782954484019467639906521)
          ·
            refine ⟨13337215863014600729929891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17782954484019467639906521 13337215863014600729929891)
            ·
              refine ⟨20005823794521901094894837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13337215863014600729929891 20005823794521901094894837)
              ·
                refine ⟨1875545980736428227646391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20005823794521901094894837 1875545980736428227646391)
                ·
                  refine ⟨2813318971104642341469587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875545980736428227646391 2813318971104642341469587)
                  ·
                    refine ⟨4219978456656963512204381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2813318971104642341469587 4219978456656963512204381)
                    ·
                      refine ⟨1582491921246361317076643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4219978456656963512204381 1582491921246361317076643)
                      ·
                        rfl

theorem cell23_3081892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_3081892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081892 prefixEnd_3081892 := by exact prefixLift 3081892
  have htrace : WordTrace (prefixWord ++ tailWord_3081892) baseStart_3081892 baseEnd_3081892 := by
    simpa [prefixWord, tailWord_3081892, baseEnd_3081892] using wordTrace_append hprefix tailTrace_3081892
  have hstable : (prefixWord ++ tailWord_3081892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081892).length < 2 ^ (prefixWord ++ tailWord_3081892).sum := by decide
  have hdescent : baseEnd_3081892 < baseStart_3081892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081918 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3081918 : Nat := 118140960795 + 3081918 * 2 ^ 59
def prefixEnd_3081918 : Nat := 4983230072969 + 3 ^ 40 * 3081918 * 2
def baseEnd_3081918 : Nat := 1582505271743378215351523

theorem tailTrace_3081918 : CollatzResearch.WordTrace tailWord_3081918 prefixEnd_3081918 1582505271743378215351523 := by
  unfold tailWord_3081918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050848006093113816833801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74937856032496607023113605 14050848006093113816833801)
  ·
    refine ⟨10538136004569835362625351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14050848006093113816833801 10538136004569835362625351)
    ·
      refine ⟨15807204006854753043938027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10538136004569835362625351 15807204006854753043938027)
      ·
        refine ⟨23710806010282129565907041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15807204006854753043938027 23710806010282129565907041)
        ·
          refine ⟨17783104507711597174430281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23710806010282129565907041 17783104507711597174430281)
          ·
            refine ⟨13337328380783697880822711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17783104507711597174430281 13337328380783697880822711)
            ·
              refine ⟨20005992571175546821234067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13337328380783697880822711 20005992571175546821234067)
              ·
                refine ⟨30008988856763320231851101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20005992571175546821234067 30008988856763320231851101)
                ·
                  refine ⟨11253370821286245086944163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30008988856763320231851101 11253370821286245086944163)
                  ·
                    refine ⟨16880056231929367630416245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11253370821286245086944163 16880056231929367630416245)
                    ·
                      refine ⟨1582505271743378215351523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16880056231929367630416245 1582505271743378215351523)
                      ·
                        rfl

theorem cell23_3081918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3081918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081918 prefixEnd_3081918 := by exact prefixLift 3081918
  have htrace : WordTrace (prefixWord ++ tailWord_3081918) baseStart_3081918 baseEnd_3081918 := by
    simpa [prefixWord, tailWord_3081918, baseEnd_3081918] using wordTrace_append hprefix tailTrace_3081918
  have hstable : (prefixWord ++ tailWord_3081918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081918).length < 2 ^ (prefixWord ++ tailWord_3081918).sum := by decide
  have hdescent : baseEnd_3081918 < baseStart_3081918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081932 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3081932 : Nat := 118140960795 + 3081932 * 2 ^ 59
def prefixEnd_3081932 : Nat := 4983230072969 + 3 ^ 40 * 3081932 * 2
def baseEnd_3081932 : Nat := 1582512460472541160576459

theorem tailTrace_3081932 : CollatzResearch.WordTrace tailWord_3081932 prefixEnd_3081932 1582512460472541160576459 := by
  unfold tailWord_3081932
  simp only [CollatzResearch.WordTrace]
  refine ⟨56203647335347095462840025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74938196447129460617120033 56203647335347095462840025)
  ·
    refine ⟨42152735501510321597130019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56203647335347095462840025 42152735501510321597130019)
    ·
      refine ⟨63229103252265482395695029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42152735501510321597130019 63229103252265482395695029)
      ·
        refine ⟨5927728429899888974596409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63229103252265482395695029 5927728429899888974596409)
        ·
          refine ⟨4445796322424916730947307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5927728429899888974596409 4445796322424916730947307)
          ·
            refine ⟨6668694483637375096420961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445796322424916730947307 6668694483637375096420961)
            ·
              refine ⟨5001520862728031322315721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6668694483637375096420961 5001520862728031322315721)
              ·
                refine ⟨3751140647046023491736791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5001520862728031322315721 3751140647046023491736791)
                ·
                  refine ⟨5626710970569035237605187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3751140647046023491736791 5626710970569035237605187)
                  ·
                    refine ⟨8440066455853552856407781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5626710970569035237605187 8440066455853552856407781)
                    ·
                      refine ⟨1582512460472541160576459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8440066455853552856407781 1582512460472541160576459)
                      ·
                        rfl

theorem cell23_3081932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3081932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081932 prefixEnd_3081932 := by exact prefixLift 3081932
  have htrace : WordTrace (prefixWord ++ tailWord_3081932) baseStart_3081932 baseEnd_3081932 := by
    simpa [prefixWord, tailWord_3081932, baseEnd_3081932] using wordTrace_append hprefix tailTrace_3081932
  have hstable : (prefixWord ++ tailWord_3081932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081932).length < 2 ^ (prefixWord ++ tailWord_3081932).sum := by decide
  have hdescent : baseEnd_3081932 < baseStart_3081932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081938 : List Nat := [3, 2, 2, 2, 2, 2, 1, 9]
def baseStart_3081938 : Nat := 118140960795 + 3081938 * 2 ^ 59
def prefixEnd_3081938 : Nat := 4983230072969 + 3 ^ 40 * 3081938 * 2
def baseEnd_3081938 : Nat := 58611686716906227300053

theorem tailTrace_3081938 : CollatzResearch.WordTrace tailWord_3081938 prefixEnd_3081938 58611686716906227300053 := by
  unfold tailWord_3081938
  simp only [CollatzResearch.WordTrace]
  refine ⟨28101878377168113487599617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74938342339114969300265645 28101878377168113487599617)
  ·
    refine ⟨21076408782876085115699713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28101878377168113487599617 21076408782876085115699713)
    ·
      refine ⟨15807306587157063836774785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21076408782876085115699713 15807306587157063836774785)
      ·
        refine ⟨11855479940367797877581089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15807306587157063836774785 11855479940367797877581089)
        ·
          refine ⟨8891609955275848408185817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11855479940367797877581089 8891609955275848408185817)
          ·
            refine ⟨6668707466456886306139363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8891609955275848408185817 6668707466456886306139363)
            ·
              refine ⟨10003061199685329459209045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668707466456886306139363 10003061199685329459209045)
              ·
                refine ⟨58611686716906227300053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10003061199685329459209045 58611686716906227300053)
                ·
                  rfl

theorem cell23_3081938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 9].length) (baseStart_3081938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081938 prefixEnd_3081938 := by exact prefixLift 3081938
  have htrace : WordTrace (prefixWord ++ tailWord_3081938) baseStart_3081938 baseEnd_3081938 := by
    simpa [prefixWord, tailWord_3081938, baseEnd_3081938] using wordTrace_append hprefix tailTrace_3081938
  have hstable : (prefixWord ++ tailWord_3081938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081938).length < 2 ^ (prefixWord ++ tailWord_3081938).sum := by decide
  have hdescent : baseEnd_3081938 < baseStart_3081938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081955 : List Nat := [1, 1, 1, 7, 3, 1, 9]
def baseStart_3081955 : Nat := 118140960795 + 3081955 * 2 ^ 59
def prefixEnd_3081955 : Nat := 4983230072969 + 3 ^ 40 * 3081955 * 2
def baseEnd_3081955 : Nat := 19537336673180179883813

theorem tailTrace_3081955 : CollatzResearch.WordTrace tailWord_3081955 prefixEnd_3081955 19537336673180179883813 := by
  unfold tailWord_3081955
  simp only [CollatzResearch.WordTrace]
  refine ⟨112408133549610865853767319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74938755699740577235844879 112408133549610865853767319)
  ·
    refine ⟨168612200324416298780650979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112408133549610865853767319 168612200324416298780650979)
    ·
      refine ⟨252918300486624448170976469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168612200324416298780650979 252918300486624448170976469)
      ·
        refine ⟨5927772667655260504007261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 252918300486624448170976469 5927772667655260504007261)
        ·
          refine ⟨2222914750370722689002723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5927772667655260504007261 2222914750370722689002723)
          ·
            refine ⟨3334372125556084033504085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222914750370722689002723 3334372125556084033504085)
            ·
              refine ⟨19537336673180179883813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3334372125556084033504085 19537336673180179883813)
              ·
                rfl

theorem cell23_3081955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 9].length) (baseStart_3081955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081955 prefixEnd_3081955 := by exact prefixLift 3081955
  have htrace : WordTrace (prefixWord ++ tailWord_3081955) baseStart_3081955 baseEnd_3081955 := by
    simpa [prefixWord, tailWord_3081955, baseEnd_3081955] using wordTrace_append hprefix tailTrace_3081955
  have hstable : (prefixWord ++ tailWord_3081955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081955).length < 2 ^ (prefixWord ++ tailWord_3081955).sum := by decide
  have hdescent : baseEnd_3081955 < baseStart_3081955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081961 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_3081961 : Nat := 118140960795 + 3081961 * 2 ^ 59
def prefixEnd_3081961 : Nat := 4983230072969 + 3 ^ 40 * 3081961 * 2
def baseEnd_3081961 : Nat := 1582527351411521547113825

theorem tailTrace_3081961 : CollatzResearch.WordTrace tailWord_3081961 prefixEnd_3081961 1582527351411521547113825 := by
  unfold tailWord_3081961
  simp only [CollatzResearch.WordTrace]
  refine ⟨112408352387589128878485737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74938901591726085918990491 112408352387589128878485737)
  ·
    refine ⟨84306264290691846658864303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112408352387589128878485737 84306264290691846658864303)
    ·
      refine ⟨126459396436037769988296455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84306264290691846658864303 126459396436037769988296455)
      ·
        refine ⟨189689094654056654982444683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126459396436037769988296455 189689094654056654982444683)
        ·
          refine ⟨284533641981084982473667025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189689094654056654982444683 284533641981084982473667025)
          ·
            refine ⟨213400231485813736855250269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284533641981084982473667025 213400231485813736855250269)
            ·
              refine ⟨80025086807180151320718851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213400231485813736855250269 80025086807180151320718851)
              ·
                refine ⟨120037630210770226981078277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80025086807180151320718851 120037630210770226981078277)
                ·
                  refine ⟨22507055664519417558952177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120037630210770226981078277 22507055664519417558952177)
                  ·
                    refine ⟨16880291748389563169214133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22507055664519417558952177 16880291748389563169214133)
                    ·
                      refine ⟨1582527351411521547113825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16880291748389563169214133 1582527351411521547113825)
                      ·
                        rfl

theorem cell23_3081961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_3081961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081961 prefixEnd_3081961 := by exact prefixLift 3081961
  have htrace : WordTrace (prefixWord ++ tailWord_3081961) baseStart_3081961 baseEnd_3081961 := by
    simpa [prefixWord, tailWord_3081961, baseEnd_3081961] using wordTrace_append hprefix tailTrace_3081961
  have hstable : (prefixWord ++ tailWord_3081961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081961).length < 2 ^ (prefixWord ++ tailWord_3081961).sum := by decide
  have hdescent : baseEnd_3081961 < baseStart_3081961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081966 : List Nat := [4, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_3081966 : Nat := 118140960795 + 3081966 * 2 ^ 59
def prefixEnd_3081966 : Nat := 4983230072969 + 3 ^ 40 * 3081966 * 2
def baseEnd_3081966 : Nat := 1582529918814794027551303

theorem tailTrace_3081966 : CollatzResearch.WordTrace tailWord_3081966 prefixEnd_3081966 1582529918814794027551303 := by
  unfold tailWord_3081966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14051066844071376841552219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74939023168380676488278501 14051066844071376841552219)
  ·
    refine ⟨21076600266107065262328329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14051066844071376841552219 21076600266107065262328329)
    ·
      refine ⟨15807450199580298946746247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21076600266107065262328329 15807450199580298946746247)
      ·
        refine ⟨23711175299370448420119371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15807450199580298946746247 23711175299370448420119371)
        ·
          refine ⟨35566762949055672630179057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23711175299370448420119371 35566762949055672630179057)
          ·
            refine ⟨26675072211791754472634293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35566762949055672630179057 26675072211791754472634293)
            ·
              refine ⟨2500788019855476981809465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26675072211791754472634293 2500788019855476981809465)
              ·
                refine ⟨1875591014891607736357099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500788019855476981809465 1875591014891607736357099)
                ·
                  refine ⟨2813386522337411604535649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875591014891607736357099 2813386522337411604535649)
                  ·
                    refine ⟨2110039891753058703401737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2813386522337411604535649 2110039891753058703401737)
                    ·
                      refine ⟨1582529918814794027551303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110039891753058703401737 1582529918814794027551303)
                      ·
                        rfl

theorem cell23_3081966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_3081966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081966 prefixEnd_3081966 := by exact prefixLift 3081966
  have htrace : WordTrace (prefixWord ++ tailWord_3081966) baseStart_3081966 baseEnd_3081966 := by
    simpa [prefixWord, tailWord_3081966, baseEnd_3081966] using wordTrace_append hprefix tailTrace_3081966
  have hstable : (prefixWord ++ tailWord_3081966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081966).length < 2 ^ (prefixWord ++ tailWord_3081966).sum := by decide
  have hdescent : baseEnd_3081966 < baseStart_3081966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3081972 : List Nat := [2, 6, 1, 1, 1, 2, 2, 8]
def baseStart_3081972 : Nat := 118140960795 + 3081972 * 2 ^ 59
def prefixEnd_3081972 : Nat := 4983230072969 + 3 ^ 40 * 3081972 * 2
def baseEnd_3081972 : Nat := 58612333322174852002825

theorem tailTrace_3081972 : CollatzResearch.WordTrace tailWord_3081972 prefixEnd_3081972 58612333322174852002825 := by
  unfold tailWord_3081972
  simp only [CollatzResearch.WordTrace]
  refine ⟨56204376795274638878568085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74939169060366185171424113 56204376795274638878568085)
  ·
    refine ⟨2634580162278498697432879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56204376795274638878568085 2634580162278498697432879)
    ·
      refine ⟨3951870243417748046149319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2634580162278498697432879 3951870243417748046149319)
      ·
        refine ⟨5927805365126622069223979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3951870243417748046149319 5927805365126622069223979)
        ·
          refine ⟨8891708047689933103835969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5927805365126622069223979 8891708047689933103835969)
          ·
            refine ⟨6668781035767449827876977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8891708047689933103835969 6668781035767449827876977)
            ·
              refine ⟨5001585776825587370907733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6668781035767449827876977 5001585776825587370907733)
              ·
                refine ⟨58612333322174852002825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5001585776825587370907733 58612333322174852002825)
                ·
                  rfl

theorem cell23_3081972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 8].length) (baseStart_3081972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3081972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3081972 prefixEnd_3081972 := by exact prefixLift 3081972
  have htrace : WordTrace (prefixWord ++ tailWord_3081972) baseStart_3081972 baseEnd_3081972 := by
    simpa [prefixWord, tailWord_3081972, baseEnd_3081972] using wordTrace_append hprefix tailTrace_3081972
  have hstable : (prefixWord ++ tailWord_3081972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3081972).length < 2 ^ (prefixWord ++ tailWord_3081972).sum := by decide
  have hdescent : baseEnd_3081972 < baseStart_3081972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3081972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082005 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_3082005 : Nat := 118140960795 + 3082005 * 2 ^ 59
def prefixEnd_3082005 : Nat := 4983230072969 + 3 ^ 40 * 3082005 * 2
def baseEnd_3082005 : Nat := 1582549944560319374963623

theorem tailTrace_3082005 : CollatzResearch.WordTrace tailWord_3082005 prefixEnd_3082005 1582549944560319374963623 := by
  unfold tailWord_3082005
  simp only [CollatzResearch.WordTrace]
  refine ⟨112409957199429724393087469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74939971466286482928724979 112409957199429724393087469)
  ·
    refine ⟨42153733949786146647407801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112409957199429724393087469 42153733949786146647407801)
    ·
      refine ⟨31615300462339609985555851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42153733949786146647407801 31615300462339609985555851)
      ·
        refine ⟨47422950693509414978333777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31615300462339609985555851 47422950693509414978333777)
        ·
          refine ⟨35567213020132061233750333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47422950693509414978333777 35567213020132061233750333)
          ·
            refine ⟨13337704882549522962656375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35567213020132061233750333 13337704882549522962656375)
            ·
              refine ⟨20006557323824284443984563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13337704882549522962656375 20006557323824284443984563)
              ·
                refine ⟨30009835985736426665976845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20006557323824284443984563 30009835985736426665976845)
                ·
                  refine ⟨11253688494651159999741317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30009835985736426665976845 11253688494651159999741317)
                  ·
                    refine ⟨2110066592747092499951497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11253688494651159999741317 2110066592747092499951497)
                    ·
                      refine ⟨1582549944560319374963623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110066592747092499951497 1582549944560319374963623)
                      ·
                        rfl

theorem cell23_3082005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_3082005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082005 prefixEnd_3082005 := by exact prefixLift 3082005
  have htrace : WordTrace (prefixWord ++ tailWord_3082005) baseStart_3082005 baseEnd_3082005 := by
    simpa [prefixWord, tailWord_3082005, baseEnd_3082005] using wordTrace_append hprefix tailTrace_3082005
  have hstable : (prefixWord ++ tailWord_3082005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082005).length < 2 ^ (prefixWord ++ tailWord_3082005).sum := by decide
  have hdescent : baseEnd_3082005 < baseStart_3082005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082008 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3082008 : Nat := 118140960795 + 3082008 * 2 ^ 59
def prefixEnd_3082008 : Nat := 4983230072969 + 3 ^ 40 * 3082008 * 2
def baseEnd_3082008 : Nat := 1582551485002282863226109

theorem tailTrace_3082008 : CollatzResearch.WordTrace tailWord_3082008 prefixEnd_3082008 1582551485002282863226109 := by
  unfold tailWord_3082008
  simp only [CollatzResearch.WordTrace]
  refine ⟨56205033309209427952723339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74940044412279237270297785 56205033309209427952723339)
  ·
    refine ⟨84307549963814141929085009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56205033309209427952723339 84307549963814141929085009)
    ·
      refine ⟨63230662472860606446813757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84307549963814141929085009 63230662472860606446813757)
      ·
        refine ⟨23711498427322727417555159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63230662472860606446813757 23711498427322727417555159)
        ·
          refine ⟨35567247640984091126332739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23711498427322727417555159 35567247640984091126332739)
          ·
            refine ⟨53350871461476136689499109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35567247640984091126332739 53350871461476136689499109)
            ·
              refine ⟨10003288399026775629281083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53350871461476136689499109 10003288399026775629281083)
              ·
                refine ⟨15004932598540163443921625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10003288399026775629281083 15004932598540163443921625)
                ·
                  refine ⟨11253699448905122582941219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15004932598540163443921625 11253699448905122582941219)
                  ·
                    refine ⟨16880549173357683874411829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11253699448905122582941219 16880549173357683874411829)
                    ·
                      refine ⟨1582551485002282863226109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16880549173357683874411829 1582551485002282863226109)
                      ·
                        rfl

theorem cell23_3082008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3082008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082008 prefixEnd_3082008 := by exact prefixLift 3082008
  have htrace : WordTrace (prefixWord ++ tailWord_3082008) baseStart_3082008 baseEnd_3082008 := by
    simpa [prefixWord, tailWord_3082008, baseEnd_3082008] using wordTrace_append hprefix tailTrace_3082008
  have hstable : (prefixWord ++ tailWord_3082008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082008).length < 2 ^ (prefixWord ++ tailWord_3082008).sum := by decide
  have hdescent : baseEnd_3082008 < baseStart_3082008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082011 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 9]
def baseStart_3082011 : Nat := 118140960795 + 3082011 * 2 ^ 59
def prefixEnd_3082011 : Nat := 4983230072969 + 3 ^ 40 * 3082011 * 2
def baseEnd_3082011 : Nat := 175839225049360705720955

theorem tailTrace_3082011 : CollatzResearch.WordTrace tailWord_3082011 prefixEnd_3082011 175839225049360705720955 := by
  unfold tailWord_3082011
  simp only [CollatzResearch.WordTrace]
  refine ⟨112410176037407987417805887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74940117358271991611870591 112410176037407987417805887)
  ·
    refine ⟨168615264056111981126708831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112410176037407987417805887 168615264056111981126708831)
    ·
      refine ⟨252922896084167971690063247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168615264056111981126708831 252922896084167971690063247)
      ·
        refine ⟨379384344126251957535094871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252922896084167971690063247 379384344126251957535094871)
        ·
          refine ⟨569076516189377936302642307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379384344126251957535094871 569076516189377936302642307)
          ·
            refine ⟨853614774284066904453963461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569076516189377936302642307 853614774284066904453963461)
            ·
              refine ⟨160052770178262544585118149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 853614774284066904453963461 160052770178262544585118149)
              ·
                refine ⟨30009894408424227109709653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160052770178262544585118149 30009894408424227109709653)
                ·
                  refine ⟨175839225049360705720955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30009894408424227109709653 175839225049360705720955)
                  ·
                    rfl

theorem cell23_3082011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 9].length) (baseStart_3082011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082011 prefixEnd_3082011 := by exact prefixLift 3082011
  have htrace : WordTrace (prefixWord ++ tailWord_3082011) baseStart_3082011 baseEnd_3082011 := by
    simpa [prefixWord, tailWord_3082011, baseEnd_3082011] using wordTrace_append hprefix tailTrace_3082011
  have hstable : (prefixWord ++ tailWord_3082011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082011).length < 2 ^ (prefixWord ++ tailWord_3082011).sum := by decide
  have hdescent : baseEnd_3082011 < baseStart_3082011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082035 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 4]
def baseStart_3082035 : Nat := 118140960795 + 3082035 * 2 ^ 59
def prefixEnd_3082035 : Nat := 4983230072969 + 3 ^ 40 * 3082035 * 2
def baseEnd_3082035 : Nat := 1582565348979954257588485

theorem tailTrace_3082035 : CollatzResearch.WordTrace tailWord_3082035 prefixEnd_3082035 1582565348979954257588485 := by
  unfold tailWord_3082035
  simp only [CollatzResearch.WordTrace]
  refine ⟨112411051389321039516679559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74940700926214026344453039 112411051389321039516679559)
  ·
    refine ⟨168616577083981559275019339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112411051389321039516679559 168616577083981559275019339)
    ·
      refine ⟨252924865625972338912529009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168616577083981559275019339 252924865625972338912529009)
      ·
        refine ⟨189693649219479254184396757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252924865625972338912529009 189693649219479254184396757)
        ·
          refine ⟨4445944903581545019946799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 189693649219479254184396757 4445944903581545019946799)
          ·
            refine ⟨6668917355372317529920199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445944903581545019946799 6668917355372317529920199)
            ·
              refine ⟨10003376033058476294880299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668917355372317529920199 10003376033058476294880299)
              ·
                refine ⟨15005064049587714442320449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10003376033058476294880299 15005064049587714442320449)
                ·
                  refine ⟨11253798037190785831740337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15005064049587714442320449 11253798037190785831740337)
                  ·
                    refine ⟨8440348527893089373805253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11253798037190785831740337 8440348527893089373805253)
                    ·
                      refine ⟨1582565348979954257588485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8440348527893089373805253 1582565348979954257588485)
                      ·
                        rfl

theorem cell23_3082035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_3082035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082035 prefixEnd_3082035 := by exact prefixLift 3082035
  have htrace : WordTrace (prefixWord ++ tailWord_3082035) baseStart_3082035 baseEnd_3082035 := by
    simpa [prefixWord, tailWord_3082035, baseEnd_3082035] using wordTrace_append hprefix tailTrace_3082035
  have hstable : (prefixWord ++ tailWord_3082035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082035).length < 2 ^ (prefixWord ++ tailWord_3082035).sum := by decide
  have hdescent : baseEnd_3082035 < baseStart_3082035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082045 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 7]
def baseStart_3082045 : Nat := 118140960795 + 3082045 * 2 ^ 59
def prefixEnd_3082045 : Nat := 4983230072969 + 3 ^ 40 * 3082045 * 2
def baseEnd_3082045 : Nat := 175841164865166579829271

theorem tailTrace_3082045 : CollatzResearch.WordTrace tailWord_3082045 prefixEnd_3082045 175841164865166579829271 := by
  unfold tailWord_3082045
  simp only [CollatzResearch.WordTrace]
  refine ⟨112411416119284811224543589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74940944079523207483029059 112411416119284811224543589)
  ·
    refine ⟨21077140522365902104601923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112411416119284811224543589 21077140522365902104601923)
    ·
      refine ⟨31615710783548853156902885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21077140522365902104601923 31615710783548853156902885)
      ·
        refine ⟨5927945771915409966919291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31615710783548853156902885 5927945771915409966919291)
        ·
          refine ⟨8891918657873114950378937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5927945771915409966919291 8891918657873114950378937)
          ·
            refine ⟨6668938993404836212784203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8891918657873114950378937 6668938993404836212784203)
            ·
              refine ⟨10003408490107254319176305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668938993404836212784203 10003408490107254319176305)
              ·
                refine ⟨7502556367580440739382229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10003408490107254319176305 7502556367580440739382229)
                ·
                  refine ⟨175841164865166579829271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7502556367580440739382229 175841164865166579829271)
                  ·
                    rfl

theorem cell23_3082045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_3082045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082045 prefixEnd_3082045 := by exact prefixLift 3082045
  have htrace : WordTrace (prefixWord ++ tailWord_3082045) baseStart_3082045 baseEnd_3082045 := by
    simpa [prefixWord, tailWord_3082045, baseEnd_3082045] using wordTrace_append hprefix tailTrace_3082045
  have hstable : (prefixWord ++ tailWord_3082045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082045).length < 2 ^ (prefixWord ++ tailWord_3082045).sum := by decide
  have hdescent : baseEnd_3082045 < baseStart_3082045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082058 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_3082058 : Nat := 118140960795 + 3082058 * 2 ^ 59
def prefixEnd_3082058 : Nat := 4983230072969 + 3 ^ 40 * 3082058 * 2
def baseEnd_3082058 : Nat := 527525719678335889200293

theorem tailTrace_3082058 : CollatzResearch.WordTrace tailWord_3082058 prefixEnd_3082058 527525719678335889200293 := by
  unfold tailWord_3082058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28102972567059428611191707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74941260178825142963177885 28102972567059428611191707)
  ·
    refine ⟨42154458850589142916787561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28102972567059428611191707 42154458850589142916787561)
    ·
      refine ⟨31615844137941857187590671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42154458850589142916787561 31615844137941857187590671)
      ·
        refine ⟨47423766206912785781386007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31615844137941857187590671 47423766206912785781386007)
        ·
          refine ⟨71135649310369178672079011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47423766206912785781386007 71135649310369178672079011)
          ·
            refine ⟨106703473965553768008118517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71135649310369178672079011 106703473965553768008118517)
            ·
              refine ⟨10003450684270665750761111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106703473965553768008118517 10003450684270665750761111)
              ·
                refine ⟨15005176026405998626141667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10003450684270665750761111 15005176026405998626141667)
                ·
                  refine ⟨22507764039608997939212501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15005176026405998626141667 22507764039608997939212501)
                  ·
                    refine ⟨527525719678335889200293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22507764039608997939212501 527525719678335889200293)
                    ·
                      rfl

theorem cell23_3082058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_3082058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082058 prefixEnd_3082058 := by exact prefixLift 3082058
  have htrace : WordTrace (prefixWord ++ tailWord_3082058) baseStart_3082058 baseEnd_3082058 := by
    simpa [prefixWord, tailWord_3082058, baseEnd_3082058] using wordTrace_append hprefix tailTrace_3082058
  have hstable : (prefixWord ++ tailWord_3082058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082058).length < 2 ^ (prefixWord ++ tailWord_3082058).sum := by decide
  have hdescent : baseEnd_3082058 < baseStart_3082058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082105 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 3, 4]
def baseStart_3082105 : Nat := 118140960795 + 3082105 * 2 ^ 59
def prefixEnd_3082105 : Nat := 4983230072969 + 3 ^ 40 * 3082105 * 2
def baseEnd_3082105 : Nat := 527533764208589661237721

theorem tailTrace_3082105 : CollatzResearch.WordTrace tailWord_3082105 prefixEnd_3082105 527533764208589661237721 := by
  unfold tailWord_3082105
  simp only [CollatzResearch.WordTrace]
  refine ⟨112413604499067441471727769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74942402999378294314485179 112413604499067441471727769)
  ·
    refine ⟨84310203374300581103795827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112413604499067441471727769 84310203374300581103795827)
    ·
      refine ⟨126465305061450871655693741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84310203374300581103795827 126465305061450871655693741)
      ·
        refine ⟨47424489398044076870885153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126465305061450871655693741 47424489398044076870885153)
        ·
          refine ⟨35568367048533057653163865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47424489398044076870885153 35568367048533057653163865)
          ·
            refine ⟨26676275286399793239872899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35568367048533057653163865 26676275286399793239872899)
            ·
              refine ⟨40014412929599689859809349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26676275286399793239872899 40014412929599689859809349)
              ·
                refine ⟨7502702424299941848714253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40014412929599689859809349 7502702424299941848714253)
                ·
                  refine ⟨2813513409112478193267845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7502702424299941848714253 2813513409112478193267845)
                  ·
                    refine ⟨527533764208589661237721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813513409112478193267845 527533764208589661237721)
                    ·
                      rfl

theorem cell23_3082105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 4].length) (baseStart_3082105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082105 prefixEnd_3082105 := by exact prefixLift 3082105
  have htrace : WordTrace (prefixWord ++ tailWord_3082105) baseStart_3082105 baseEnd_3082105 := by
    simpa [prefixWord, tailWord_3082105, baseEnd_3082105] using wordTrace_append hprefix tailTrace_3082105
  have hstable : (prefixWord ++ tailWord_3082105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082105).length < 2 ^ (prefixWord ++ tailWord_3082105).sum := by decide
  have hdescent : baseEnd_3082105 < baseStart_3082105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082115 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 3]
def baseStart_3082115 : Nat := 118140960795 + 3082115 * 2 ^ 59
def prefixEnd_3082115 : Nat := 4983230072969 + 3 ^ 40 * 3082115 * 2
def baseEnd_3082115 : Nat := 1582606427432313944588117

theorem tailTrace_3082115 : CollatzResearch.WordTrace tailWord_3082115 prefixEnd_3082115 1582606427432313944588117 := by
  unfold tailWord_3082115
  simp only [CollatzResearch.WordTrace]
  refine ⟨112413969229031213179591799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74942646152687475453061199 112413969229031213179591799)
  ·
    refine ⟨168620953843546819769387699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112413969229031213179591799 168620953843546819769387699)
    ·
      refine ⟨252931430765320229654081549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168620953843546819769387699 252931430765320229654081549)
      ·
        refine ⟨94849286536995086120280581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252931430765320229654081549 94849286536995086120280581)
        ·
          refine ⟨17784241225686578647552609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94849286536995086120280581 17784241225686578647552609)
          ·
            refine ⟨13338180919264933985664457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17784241225686578647552609 13338180919264933985664457)
            ·
              refine ⟨10003635689448700489248343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13338180919264933985664457 10003635689448700489248343)
              ·
                refine ⟨15005453534173050733872515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10003635689448700489248343 15005453534173050733872515)
                ·
                  refine ⟨22508180301259576100808773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15005453534173050733872515 22508180301259576100808773)
                  ·
                    refine ⟨4220283806486170518901645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22508180301259576100808773 4220283806486170518901645)
                    ·
                      refine ⟨1582606427432313944588117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4220283806486170518901645 1582606427432313944588117)
                      ·
                        rfl

theorem cell23_3082115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_3082115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082115 prefixEnd_3082115 := by exact prefixLift 3082115
  have htrace : WordTrace (prefixWord ++ tailWord_3082115) baseStart_3082115 baseEnd_3082115 := by
    simpa [prefixWord, tailWord_3082115, baseEnd_3082115] using wordTrace_append hprefix tailTrace_3082115
  have hstable : (prefixWord ++ tailWord_3082115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082115).length < 2 ^ (prefixWord ++ tailWord_3082115).sum := by decide
  have hdescent : baseEnd_3082115 < baseStart_3082115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082132 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_3082132 : Nat := 118140960795 + 3082132 * 2 ^ 59
def prefixEnd_3082132 : Nat := 4983230072969 + 3 ^ 40 * 3082132 * 2
def baseEnd_3082132 : Nat := 1582615156603440378075539

theorem tailTrace_3082132 : CollatzResearch.WordTrace tailWord_3082132 prefixEnd_3082132 1582615156603440378075539 := by
  unfold tailWord_3082132
  simp only [CollatzResearch.WordTrace]
  refine ⟨56207294634984812541480325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74943059513313083388640433 56207294634984812541480325)
  ·
    refine ⟨10538867744059652351527561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56207294634984812541480325 10538867744059652351527561)
    ·
      refine ⟨7904150808044739263645671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10538867744059652351527561 7904150808044739263645671)
      ·
        refine ⟨11856226212067108895468507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7904150808044739263645671 11856226212067108895468507)
        ·
          refine ⟨17784339318100663343202761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11856226212067108895468507 17784339318100663343202761)
          ·
            refine ⟨13338254488575497507402071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17784339318100663343202761 13338254488575497507402071)
            ·
              refine ⟨20007381732863246261103107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13338254488575497507402071 20007381732863246261103107)
              ·
                refine ⟨30011072599294869391654661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20007381732863246261103107 30011072599294869391654661)
                ·
                  refine ⟨5627076112367788010935249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30011072599294869391654661 5627076112367788010935249)
                  ·
                    refine ⟨4220307084275841008201437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5627076112367788010935249 4220307084275841008201437)
                    ·
                      refine ⟨1582615156603440378075539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4220307084275841008201437 1582615156603440378075539)
                      ·
                        rfl

theorem cell23_3082132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_3082132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082132 prefixEnd_3082132 := by exact prefixLift 3082132
  have htrace : WordTrace (prefixWord ++ tailWord_3082132) baseStart_3082132 baseEnd_3082132 := by
    simpa [prefixWord, tailWord_3082132, baseEnd_3082132] using wordTrace_append hprefix tailTrace_3082132
  have hstable : (prefixWord ++ tailWord_3082132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082132).length < 2 ^ (prefixWord ++ tailWord_3082132).sum := by decide
  have hdescent : baseEnd_3082132 < baseStart_3082132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082162 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_3082162 : Nat := 118140960795 + 3082162 * 2 ^ 59
def prefixEnd_3082162 : Nat := 4983230072969 + 3 ^ 40 * 3082162 * 2
def baseEnd_3082162 : Nat := 1582630561023075260700401

theorem tailTrace_3082162 : CollatzResearch.WordTrace tailWord_3082162 prefixEnd_3082162 1582630561023075260700401 := by
  unfold tailWord_3082162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28103920864965235051638185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74943788973240626804368493 28103920864965235051638185)
  ·
    refine ⟨21077940648723926288728639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28103920864965235051638185 21077940648723926288728639)
    ·
      refine ⟨31616910973085889433092959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21077940648723926288728639 31616910973085889433092959)
      ·
        refine ⟨47425366459628834149639439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31616910973085889433092959 47425366459628834149639439)
        ·
          refine ⟨71138049689443251224459159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47425366459628834149639439 71138049689443251224459159)
          ·
            refine ⟨106707074534164876836688739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71138049689443251224459159 106707074534164876836688739)
            ·
              refine ⟨160060611801247315255033109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106707074534164876836688739 160060611801247315255033109)
              ·
                refine ⟨7502841178183467902579677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160060611801247315255033109 7502841178183467902579677)
                ·
                  refine ⟨2813565441818800463467379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7502841178183467902579677 2813565441818800463467379)
                  ·
                    refine ⟨4220348162728200695201069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2813565441818800463467379 4220348162728200695201069)
                    ·
                      refine ⟨1582630561023075260700401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4220348162728200695201069 1582630561023075260700401)
                      ·
                        rfl

theorem cell23_3082162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_3082162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082162 prefixEnd_3082162 := by exact prefixLift 3082162
  have htrace : WordTrace (prefixWord ++ tailWord_3082162) baseStart_3082162 baseEnd_3082162 := by
    simpa [prefixWord, tailWord_3082162, baseEnd_3082162] using wordTrace_append hprefix tailTrace_3082162
  have hstable : (prefixWord ++ tailWord_3082162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082162).length < 2 ^ (prefixWord ++ tailWord_3082162).sum := by decide
  have hdescent : baseEnd_3082162 < baseStart_3082162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082196 : List Nat := [2, 4, 1, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_3082196 : Nat := 118140960795 + 3082196 * 2 ^ 59
def prefixEnd_3082196 : Nat := 4983230072969 + 3 ^ 40 * 3082196 * 2
def baseEnd_3082196 : Nat := 1582648019365328127675245

theorem tailTrace_3082196 : CollatzResearch.WordTrace tailWord_3082196 prefixEnd_3082196 1582648019365328127675245 := by
  unfold tailWord_3082196
  simp only [CollatzResearch.WordTrace]
  refine ⟨56208461770868882006645221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74944615694491842675526961 56208461770868882006645221)
  ·
    refine ⟨10539086582037915376245979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56208461770868882006645221 10539086582037915376245979)
    ·
      refine ⟨15808629873056873064368969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10539086582037915376245979 15808629873056873064368969)
      ·
        refine ⟨11856472404792654798276727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15808629873056873064368969 11856472404792654798276727)
        ·
          refine ⟨17784708607188982197415091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11856472404792654798276727 17784708607188982197415091)
          ·
            refine ⟨26677062910783473296122637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17784708607188982197415091 26677062910783473296122637)
            ·
              refine ⟨10003898591543802486045989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26677062910783473296122637 10003898591543802486045989)
              ·
                refine ⟨1875730985914462966133623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10003898591543802486045989 1875730985914462966133623)
                ·
                  refine ⟨2813596478871694449200435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875730985914462966133623 2813596478871694449200435)
                  ·
                    refine ⟨4220394718307541673800653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2813596478871694449200435 4220394718307541673800653)
                    ·
                      refine ⟨1582648019365328127675245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4220394718307541673800653 1582648019365328127675245)
                      ·
                        rfl

theorem cell23_3082196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_3082196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082196 prefixEnd_3082196 := by exact prefixLift 3082196
  have htrace : WordTrace (prefixWord ++ tailWord_3082196) baseStart_3082196 baseEnd_3082196 := by
    simpa [prefixWord, tailWord_3082196, baseEnd_3082196] using wordTrace_append hprefix tailTrace_3082196
  have hstable : (prefixWord ++ tailWord_3082196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082196).length < 2 ^ (prefixWord ++ tailWord_3082196).sum := by decide
  have hdescent : baseEnd_3082196 < baseStart_3082196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082212 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_3082212 : Nat := 118140960795 + 3082212 * 2 ^ 59
def prefixEnd_3082212 : Nat := 4983230072969 + 3 ^ 40 * 3082212 * 2
def baseEnd_3082212 : Nat := 527552078351933355025057

theorem tailTrace_3082212 : CollatzResearch.WordTrace tailWord_3082212 prefixEnd_3082212 527552078351933355025057 := by
  unfold tailWord_3082212
  simp only [CollatzResearch.WordTrace]
  refine ⟨56208753554839899372936445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74945004739786532497248593 56208753554839899372936445)
  ·
    refine ⟨21078282583064962264851167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56208753554839899372936445 21078282583064962264851167)
    ·
      refine ⟨31617423874597443397276751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21078282583064962264851167 31617423874597443397276751)
      ·
        refine ⟨47426135811896165095915127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31617423874597443397276751 47426135811896165095915127)
        ·
          refine ⟨71139203717844247643872691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47426135811896165095915127 71139203717844247643872691)
          ·
            refine ⟨106708805576766371465809037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71139203717844247643872691 106708805576766371465809037)
            ·
              refine ⟨40015802091287389299678389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106708805576766371465809037 40015802091287389299678389)
              ·
                refine ⟨3751481446058192746844849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40015802091287389299678389 3751481446058192746844849)
                ·
                  refine ⟨2813611084543644560133637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3751481446058192746844849 2813611084543644560133637)
                  ·
                    refine ⟨527552078351933355025057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813611084543644560133637 527552078351933355025057)
                    ·
                      rfl

theorem cell23_3082212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_3082212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082212 prefixEnd_3082212 := by exact prefixLift 3082212
  have htrace : WordTrace (prefixWord ++ tailWord_3082212) baseStart_3082212 baseEnd_3082212 := by
    simpa [prefixWord, tailWord_3082212, baseEnd_3082212] using wordTrace_append hprefix tailTrace_3082212
  have hstable : (prefixWord ++ tailWord_3082212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082212).length < 2 ^ (prefixWord ++ tailWord_3082212).sum := by decide
  have hdescent : baseEnd_3082212 < baseStart_3082212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082269 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_3082269 : Nat := 118140960795 + 3082269 * 2 ^ 59
def prefixEnd_3082269 : Nat := 4983230072969 + 3 ^ 40 * 3082269 * 2
def baseEnd_3082269 : Nat := 1582685503453106342062409

theorem tailTrace_3082269 : CollatzResearch.WordTrace tailWord_3082269 prefixEnd_3082269 1582685503453106342062409 := by
  unfold tailWord_3082269
  simp only [CollatzResearch.WordTrace]
  refine ⟨112419586070473297480697861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74946390713648864987131907 112419586070473297480697861)
  ·
    refine ⟨21078672388213743277630849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112419586070473297480697861 21078672388213743277630849)
    ·
      refine ⟨15809004291160307458223137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21078672388213743277630849 15809004291160307458223137)
      ·
        refine ⟨11856753218370230593667353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15809004291160307458223137 11856753218370230593667353)
        ·
          refine ⟨8892564913777672945250515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11856753218370230593667353 8892564913777672945250515)
          ·
            refine ⟨13338847370666509417875773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8892564913777672945250515 13338847370666509417875773)
            ·
              refine ⟨5002067763999941031703415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13338847370666509417875773 5002067763999941031703415)
              ·
                refine ⟨7503101645999911547555123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002067763999941031703415 7503101645999911547555123)
                ·
                  refine ⟨11254652468999867321332685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7503101645999911547555123 11254652468999867321332685)
                  ·
                    refine ⟨4220494675874950245499757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11254652468999867321332685 4220494675874950245499757)
                    ·
                      refine ⟨1582685503453106342062409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4220494675874950245499757 1582685503453106342062409)
                      ·
                        rfl

theorem cell23_3082269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_3082269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082269 prefixEnd_3082269 := by exact prefixLift 3082269
  have htrace : WordTrace (prefixWord ++ tailWord_3082269) baseStart_3082269 baseEnd_3082269 := by
    simpa [prefixWord, tailWord_3082269, baseEnd_3082269] using wordTrace_append hprefix tailTrace_3082269
  have hstable : (prefixWord ++ tailWord_3082269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082269).length < 2 ^ (prefixWord ++ tailWord_3082269).sum := by decide
  have hdescent : baseEnd_3082269 < baseStart_3082269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082276 : List Nat := [2, 3, 1, 4, 3, 1, 2, 7]
def baseStart_3082276 : Nat := 118140960795 + 3082276 * 2 ^ 59
def prefixEnd_3082276 : Nat := 4983230072969 + 3 ^ 40 * 3082276 * 2
def baseEnd_3082276 : Nat := 58618114733988437580551

theorem tailTrace_3082276 : CollatzResearch.WordTrace tailWord_3082276 prefixEnd_3082276 58618114733988437580551 := by
  unfold tailWord_3082276
  simp only [CollatzResearch.WordTrace]
  refine ⟨56209920690723968838101341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74946560920965291784135121 56209920690723968838101341)
  ·
    refine ⟨21078720259021488314288003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56209920690723968838101341 21078720259021488314288003)
    ·
      refine ⟨31618080388532232471432005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21078720259021488314288003 31618080388532232471432005)
      ·
        refine ⟨5928390072849793588393501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31618080388532232471432005 5928390072849793588393501)
        ·
          refine ⟨2223146277318672595647563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5928390072849793588393501 2223146277318672595647563)
          ·
            refine ⟨3334719415978008893471345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223146277318672595647563 3334719415978008893471345)
            ·
              refine ⟨2501039561983506670103509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3334719415978008893471345 2501039561983506670103509)
              ·
                refine ⟨58618114733988437580551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2501039561983506670103509 58618114733988437580551)
                ·
                  rfl

theorem cell23_3082276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 7].length) (baseStart_3082276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082276 prefixEnd_3082276 := by exact prefixLift 3082276
  have htrace : WordTrace (prefixWord ++ tailWord_3082276) baseStart_3082276 baseEnd_3082276 := by
    simpa [prefixWord, tailWord_3082276, baseEnd_3082276] using wordTrace_append hprefix tailTrace_3082276
  have hstable : (prefixWord ++ tailWord_3082276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082276).length < 2 ^ (prefixWord ++ tailWord_3082276).sum := by decide
  have hdescent : baseEnd_3082276 < baseStart_3082276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082282 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3082282 : Nat := 118140960795 + 3082282 * 2 ^ 59
def prefixEnd_3082282 : Nat := 4983230072969 + 3 ^ 40 * 3082282 * 2
def baseEnd_3082282 : Nat := 1582692178701614791199849

theorem tailTrace_3082282 : CollatzResearch.WordTrace tailWord_3082282 prefixEnd_3082282 1582692178701614791199849 := by
  unfold tailWord_3082282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28105015054856550175230275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74946706812950800467280733 28105015054856550175230275)
  ·
    refine ⟨42157522582284825262845413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28105015054856550175230275 42157522582284825262845413)
    ·
      refine ⟨7904535484178404736783515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42157522582284825262845413 7904535484178404736783515)
      ·
        refine ⟨11856803226267607105175273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7904535484178404736783515 11856803226267607105175273)
        ·
          refine ⟨8892602419700705328881455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11856803226267607105175273 8892602419700705328881455)
          ·
            refine ⟨13338903629551057993322183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8892602419700705328881455 13338903629551057993322183)
            ·
              refine ⟨20008355444326586989983275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13338903629551057993322183 20008355444326586989983275)
              ·
                refine ⟨30012533166489880484974913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20008355444326586989983275 30012533166489880484974913)
                ·
                  refine ⟨22509399874867410363731185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30012533166489880484974913 22509399874867410363731185)
                  ·
                    refine ⟨16882049906150557772798389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22509399874867410363731185 16882049906150557772798389)
                    ·
                      refine ⟨1582692178701614791199849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16882049906150557772798389 1582692178701614791199849)
                      ·
                        rfl

theorem cell23_3082282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3082282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082282 prefixEnd_3082282 := by exact prefixLift 3082282
  have htrace : WordTrace (prefixWord ++ tailWord_3082282) baseStart_3082282 baseEnd_3082282 := by
    simpa [prefixWord, tailWord_3082282, baseEnd_3082282] using wordTrace_append hprefix tailTrace_3082282
  have hstable : (prefixWord ++ tailWord_3082282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082282).length < 2 ^ (prefixWord ++ tailWord_3082282).sum := by decide
  have hdescent : baseEnd_3082282 < baseStart_3082282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082295 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_3082295 : Nat := 118140960795 + 3082295 * 2 ^ 59
def prefixEnd_3082295 : Nat := 4983230072969 + 3 ^ 40 * 3082295 * 2
def baseEnd_3082295 : Nat := 1582698853950123240337289

theorem tailTrace_3082295 : CollatzResearch.WordTrace tailWord_3082295 prefixEnd_3082295 1582698853950123240337289 := by
  unfold tailWord_3082295
  simp only [CollatzResearch.WordTrace]
  refine ⟨112420534368379103921144339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74947022912252735947429559 112420534368379103921144339)
  ·
    refine ⟨168630801552568655881716509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112420534368379103921144339 168630801552568655881716509)
    ·
      refine ⟨63236550582213245955643691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168630801552568655881716509 63236550582213245955643691)
      ·
        refine ⟨94854825873319868933465537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63236550582213245955643691 94854825873319868933465537)
        ·
          refine ⟨71141119404989901700099153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94854825873319868933465537 71141119404989901700099153)
          ·
            refine ⟨53355839553742426275074365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71141119404989901700099153 53355839553742426275074365)
            ·
              refine ⟨20008439832653409853152887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53355839553742426275074365 20008439832653409853152887)
              ·
                refine ⟨30012659748980114779729331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20008439832653409853152887 30012659748980114779729331)
                ·
                  refine ⟨45018989623470172169593997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30012659748980114779729331 45018989623470172169593997)
                  ·
                    refine ⟨16882121108801314563597749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45018989623470172169593997 16882121108801314563597749)
                    ·
                      refine ⟨1582698853950123240337289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16882121108801314563597749 1582698853950123240337289)
                      ·
                        rfl

theorem cell23_3082295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_3082295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082295 prefixEnd_3082295 := by exact prefixLift 3082295
  have htrace : WordTrace (prefixWord ++ tailWord_3082295) baseStart_3082295 baseEnd_3082295 := by
    simpa [prefixWord, tailWord_3082295, baseEnd_3082295] using wordTrace_append hprefix tailTrace_3082295
  have hstable : (prefixWord ++ tailWord_3082295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082295).length < 2 ^ (prefixWord ++ tailWord_3082295).sum := by decide
  have hdescent : baseEnd_3082295 < baseStart_3082295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082349 : List Nat := [1, 5, 1, 1, 2, 1, 2, 5, 5]
def baseStart_3082349 : Nat := 118140960795 + 3082349 * 2 ^ 59
def prefixEnd_3082349 : Nat := 4983230072969 + 3 ^ 40 * 3082349 * 2
def baseEnd_3082349 : Nat := 175858509100607336562449

theorem tailTrace_3082349 : CollatzResearch.WordTrace tailWord_3082349 prefixEnd_3082349 175858509100607336562449 := by
  unfold tailWord_3082349
  simp only [CollatzResearch.WordTrace]
  refine ⟨112422503910183471143610101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74948335940122314095740067 112422503910183471143610101)
  ·
    refine ⟨10539609741579700419713447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112422503910183471143610101 10539609741579700419713447)
    ·
      refine ⟨15809414612369550629570171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10539609741579700419713447 15809414612369550629570171)
      ·
        refine ⟨23714121918554325944355257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15809414612369550629570171 23714121918554325944355257)
        ·
          refine ⟨17785591438915744458266443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23714121918554325944355257 17785591438915744458266443)
          ·
            refine ⟨26678387158373616687399665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17785591438915744458266443 26678387158373616687399665)
            ·
              refine ⟨20008790368780212515549749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26678387158373616687399665 20008790368780212515549749)
              ·
                refine ⟨1875824097073144923332789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20008790368780212515549749 1875824097073144923332789)
                ·
                  refine ⟨175858509100607336562449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1875824097073144923332789 175858509100607336562449)
                  ·
                    rfl

theorem cell23_3082349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_3082349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082349 prefixEnd_3082349 := by exact prefixLift 3082349
  have htrace : WordTrace (prefixWord ++ tailWord_3082349) baseStart_3082349 baseEnd_3082349 := by
    simpa [prefixWord, tailWord_3082349, baseEnd_3082349] using wordTrace_append hprefix tailTrace_3082349
  have hstable : (prefixWord ++ tailWord_3082349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082349).length < 2 ^ (prefixWord ++ tailWord_3082349).sum := by decide
  have hdescent : baseEnd_3082349 < baseStart_3082349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082372 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3082372 : Nat := 118140960795 + 3082372 * 2 ^ 59
def prefixEnd_3082372 : Nat := 4983230072969 + 3 ^ 40 * 3082372 * 2
def baseEnd_3082372 : Nat := 1582738391960519439074435

theorem tailTrace_3082372 : CollatzResearch.WordTrace tailWord_3082372 prefixEnd_3082372 1582738391960519439074435 := by
  unfold tailWord_3082372
  simp only [CollatzResearch.WordTrace]
  refine ⟨56211671394550073035848685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74948895192733430714464913 56211671394550073035848685)
  ·
    refine ⟨21079376772956277388443257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56211671394550073035848685 21079376772956277388443257)
    ·
      refine ⟨15809532579717208041332443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21079376772956277388443257 15809532579717208041332443)
      ·
        refine ⟨23714298869575812061998665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15809532579717208041332443 23714298869575812061998665)
        ·
          refine ⟨17785724152181859046498999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23714298869575812061998665 17785724152181859046498999)
          ·
            refine ⟨26678586228272788569748499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17785724152181859046498999 26678586228272788569748499)
            ·
              refine ⟨40017879342409182854622749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26678586228272788569748499 40017879342409182854622749)
              ·
                refine ⟨15006704753403443570483531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40017879342409182854622749 15006704753403443570483531)
                ·
                  refine ⟨22510057130105165355725297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15006704753403443570483531 22510057130105165355725297)
                  ·
                    refine ⟨16882542847578874016793973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22510057130105165355725297 16882542847578874016793973)
                    ·
                      refine ⟨1582738391960519439074435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16882542847578874016793973 1582738391960519439074435)
                      ·
                        rfl

theorem cell23_3082372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3082372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082372 prefixEnd_3082372 := by exact prefixLift 3082372
  have htrace : WordTrace (prefixWord ++ tailWord_3082372) baseStart_3082372 baseEnd_3082372 := by
    simpa [prefixWord, tailWord_3082372, baseEnd_3082372] using wordTrace_append hprefix tailTrace_3082372
  have hstable : (prefixWord ++ tailWord_3082372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082372).length < 2 ^ (prefixWord ++ tailWord_3082372).sum := by decide
  have hdescent : baseEnd_3082372 < baseStart_3082372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082399 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3082399 : Nat := 118140960795 + 3082399 * 2 ^ 59
def prefixEnd_3082399 : Nat := 4983230072969 + 3 ^ 40 * 3082399 * 2
def baseEnd_3082399 : Nat := 1582752255938190833436811

theorem tailTrace_3082399 : CollatzResearch.WordTrace tailWord_3082399 prefixEnd_3082399 1582752255938190833436811 := by
  unfold tailWord_3082399
  simp only [CollatzResearch.WordTrace]
  refine ⟨112424327560002329682930251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74949551706668219788620167 112424327560002329682930251)
  ·
    refine ⟨168636491340003494524395377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112424327560002329682930251 168636491340003494524395377)
    ·
      refine ⟨126477368505002620893296533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168636491340003494524395377 126477368505002620893296533)
      ·
        refine ⟨5928626648671997854373275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126477368505002620893296533 5928626648671997854373275)
        ·
          refine ⟨8892939973007996781559913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5928626648671997854373275 8892939973007996781559913)
          ·
            refine ⟨6669704979755997586169935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8892939973007996781559913 6669704979755997586169935)
            ·
              refine ⟨10004557469633996379254903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6669704979755997586169935 10004557469633996379254903)
              ·
                refine ⟨15006836204450994568882355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10004557469633996379254903 15006836204450994568882355)
                ·
                  refine ⟨22510254306676491853323533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15006836204450994568882355 22510254306676491853323533)
                  ·
                    refine ⟨8441345365003684444996325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22510254306676491853323533 8441345365003684444996325)
                    ·
                      refine ⟨1582752255938190833436811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8441345365003684444996325 1582752255938190833436811)
                      ·
                        rfl

theorem cell23_3082399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3082399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082399 prefixEnd_3082399 := by exact prefixLift 3082399
  have htrace : WordTrace (prefixWord ++ tailWord_3082399) baseStart_3082399 baseEnd_3082399 := by
    simpa [prefixWord, tailWord_3082399, baseEnd_3082399] using wordTrace_append hprefix tailTrace_3082399
  have hstable : (prefixWord ++ tailWord_3082399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082399).length < 2 ^ (prefixWord ++ tailWord_3082399).sum := by decide
  have hdescent : baseEnd_3082399 < baseStart_3082399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082426 : List Nat := [3, 1, 1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_3082426 : Nat := 118140960795 + 3082426 * 2 ^ 59
def prefixEnd_3082426 : Nat := 4983230072969 + 3 ^ 40 * 3082426 * 2
def baseEnd_3082426 : Nat := 527588706638620742599729

theorem tailTrace_3082426 : CollatzResearch.WordTrace tailWord_3082426 prefixEnd_3082426 527588706638620742599729 := by
  unfold tailWord_3082426
  simp only [CollatzResearch.WordTrace]
  refine ⟨28106328082726128323540783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74950208220603008862775421 28106328082726128323540783)
  ·
    refine ⟨42159492124089192485311175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28106328082726128323540783 42159492124089192485311175)
    ·
      refine ⟨63239238186133788727966763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42159492124089192485311175 63239238186133788727966763)
      ·
        refine ⟨94858857279200683091950145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63239238186133788727966763 94858857279200683091950145)
        ·
          refine ⟨71144142959400512318962609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94858857279200683091950145 71144142959400512318962609)
          ·
            refine ⟨53358107219550384239221957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71144142959400512318962609 53358107219550384239221957)
            ·
              refine ⟨10004645103665697044854117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53358107219550384239221957 10004645103665697044854117)
              ·
                refine ⟨1875870956937318195910147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10004645103665697044854117 1875870956937318195910147)
                ·
                  refine ⟨2813806435405977293865221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875870956937318195910147 2813806435405977293865221)
                  ·
                    refine ⟨527588706638620742599729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813806435405977293865221 527588706638620742599729)
                    ·
                      rfl

theorem cell23_3082426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_3082426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082426 prefixEnd_3082426 := by exact prefixLift 3082426
  have htrace : WordTrace (prefixWord ++ tailWord_3082426) baseStart_3082426 baseEnd_3082426 := by
    simpa [prefixWord, tailWord_3082426, baseEnd_3082426] using wordTrace_append hprefix tailTrace_3082426
  have hstable : (prefixWord ++ tailWord_3082426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082426).length < 2 ^ (prefixWord ++ tailWord_3082426).sum := by decide
  have hdescent : baseEnd_3082426 < baseStart_3082426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082442 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3082442 : Nat := 118140960795 + 3082442 * 2 ^ 59
def prefixEnd_3082442 : Nat := 4983230072969 + 3 ^ 40 * 3082442 * 2
def baseEnd_3082442 : Nat := 1582774335606334165199113

theorem tailTrace_3082442 : CollatzResearch.WordTrace tailWord_3082442 prefixEnd_3082442 1582774335606334165199113 := by
  unfold tailWord_3082442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28106473974711637006686395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74950597265897698684497053 28106473974711637006686395)
  ·
    refine ⟨42159710962067455510029593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28106473974711637006686395 42159710962067455510029593)
    ·
      refine ⟨31619783221550591632522195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42159710962067455510029593 31619783221550591632522195)
      ·
        refine ⟨47429674832325887448783293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31619783221550591632522195 47429674832325887448783293)
        ·
          refine ⟨17786128062122207793293735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47429674832325887448783293 17786128062122207793293735)
          ·
            refine ⟨26679192093183311689940603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17786128062122207793293735 26679192093183311689940603)
            ·
              refine ⟨40018788139774967534910905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26679192093183311689940603 40018788139774967534910905)
              ·
                refine ⟨30014091104831225651183179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40018788139774967534910905 30014091104831225651183179)
                ·
                  refine ⟨45021136657246838476774769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30014091104831225651183179 45021136657246838476774769)
                  ·
                    refine ⟨33765852492935128857581077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45021136657246838476774769 33765852492935128857581077)
                    ·
                      refine ⟨1582774335606334165199113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33765852492935128857581077 1582774335606334165199113)
                      ·
                        rfl

theorem cell23_3082442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3082442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082442 prefixEnd_3082442 := by exact prefixLift 3082442
  have htrace : WordTrace (prefixWord ++ tailWord_3082442) baseStart_3082442 baseEnd_3082442 := by
    simpa [prefixWord, tailWord_3082442, baseEnd_3082442] using wordTrace_append hprefix tailTrace_3082442
  have hstable : (prefixWord ++ tailWord_3082442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082442).length < 2 ^ (prefixWord ++ tailWord_3082442).sum := by decide
  have hdescent : baseEnd_3082442 < baseStart_3082442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082476 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 2, 3, 2]
def baseStart_3082476 : Nat := 118140960795 + 3082476 * 2 ^ 59
def prefixEnd_3082476 : Nat := 4983230072969 + 3 ^ 40 * 3082476 * 2
def baseEnd_3082476 : Nat := 1582791793948587032173957

theorem tailTrace_3082476 : CollatzResearch.WordTrace tailWord_3082476 prefixEnd_3082476 1582791793948587032173957 := by
  unfold tailWord_3082476
  simp only [CollatzResearch.WordTrace]
  refine ⟨56213567990361685916741641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74951423987148914555655521 56213567990361685916741641)
  ·
    refine ⟨42160175992771264437556231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56213567990361685916741641 42160175992771264437556231)
    ·
      refine ⟨63240263989156896656334347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42160175992771264437556231 63240263989156896656334347)
      ·
        refine ⟨94860395983735344984501521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63240263989156896656334347 94860395983735344984501521)
        ·
          refine ⟨71145296987801508738376141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94860395983735344984501521 71145296987801508738376141)
          ·
            refine ⟨26679486370425565776891053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71145296987801508738376141 26679486370425565776891053)
            ·
              refine ⟨10004807388909587166334145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26679486370425565776891053 10004807388909587166334145)
              ·
                refine ⟨7503605541682190374750609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10004807388909587166334145 7503605541682190374750609)
                ·
                  refine ⟨5627704156261642781062957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7503605541682190374750609 5627704156261642781062957)
                  ·
                    refine ⟨2110389058598116042898609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5627704156261642781062957 2110389058598116042898609)
                    ·
                      refine ⟨1582791793948587032173957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110389058598116042898609 1582791793948587032173957)
                      ·
                        rfl

theorem cell23_3082476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_3082476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082476 prefixEnd_3082476 := by exact prefixLift 3082476
  have htrace : WordTrace (prefixWord ++ tailWord_3082476) baseStart_3082476 baseEnd_3082476 := by
    simpa [prefixWord, tailWord_3082476, baseEnd_3082476] using wordTrace_append hprefix tailTrace_3082476
  have hstable : (prefixWord ++ tailWord_3082476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082476).length < 2 ^ (prefixWord ++ tailWord_3082476).sum := by decide
  have hdescent : baseEnd_3082476 < baseStart_3082476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082489 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 2, 6, 2]
def baseStart_3082489 : Nat := 118140960795 + 3082489 * 2 ^ 59
def prefixEnd_3082489 : Nat := 4983230072969 + 3 ^ 40 * 3082489 * 2
def baseEnd_3082489 : Nat := 1582798469197095481311397

theorem tailTrace_3082489 : CollatzResearch.WordTrace tailWord_3082489 prefixEnd_3082489 1582798469197095481311397 := by
  unfold tailWord_3082489
  simp only [CollatzResearch.WordTrace]
  refine ⟨112427610129676275053706521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74951740086450850035804347 112427610129676275053706521)
  ·
    refine ⟨84320707597257206290279891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112427610129676275053706521 84320707597257206290279891)
    ·
      refine ⟨126481061395885809435419837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84320707597257206290279891 126481061395885809435419837)
      ·
        refine ⟨47430398023457178538282439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126481061395885809435419837 47430398023457178538282439)
        ·
          refine ⟨71145597035185767807423659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47430398023457178538282439 71145597035185767807423659)
          ·
            refine ⟨106718395552778651711135489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71145597035185767807423659 106718395552778651711135489)
            ·
              refine ⟨80038796664583988783351617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106718395552778651711135489 80038796664583988783351617)
              ·
                refine ⟨60029097498437991587513713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80038796664583988783351617 60029097498437991587513713)
                ·
                  refine ⟨45021823123828493690635285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60029097498437991587513713 45021823123828493690635285)
                  ·
                    refine ⟨2110397958929460641748529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45021823123828493690635285 2110397958929460641748529)
                    ·
                      refine ⟨1582798469197095481311397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110397958929460641748529 1582798469197095481311397)
                      ·
                        rfl

theorem cell23_3082489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_3082489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082489 prefixEnd_3082489 := by exact prefixLift 3082489
  have htrace : WordTrace (prefixWord ++ tailWord_3082489) baseStart_3082489 baseEnd_3082489 := by
    simpa [prefixWord, tailWord_3082489, baseEnd_3082489] using wordTrace_append hprefix tailTrace_3082489
  have hstable : (prefixWord ++ tailWord_3082489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082489).length < 2 ^ (prefixWord ++ tailWord_3082489).sum := by decide
  have hdescent : baseEnd_3082489 < baseStart_3082489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082506 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_3082506 : Nat := 118140960795 + 3082506 * 2 ^ 59
def prefixEnd_3082506 : Nat := 4983230072969 + 3 ^ 40 * 3082506 * 2
def baseEnd_3082506 : Nat := 1582807198368221914798819

theorem tailTrace_3082506 : CollatzResearch.WordTrace tailWord_3082506 prefixEnd_3082506 1582807198368221914798819 := by
  unfold tailWord_3082506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28107057542653671739268843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74952153447076457971383581 28107057542653671739268843)
  ·
    refine ⟨42160586313980507608903265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28107057542653671739268843 42160586313980507608903265)
    ·
      refine ⟨31620439735485380706677449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42160586313980507608903265 31620439735485380706677449)
      ·
        refine ⟨23715329801614035530008087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31620439735485380706677449 23715329801614035530008087)
        ·
          refine ⟨35572994702421053295012131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23715329801614035530008087 35572994702421053295012131)
          ·
            refine ⟨53359492053631579942518197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35572994702421053295012131 53359492053631579942518197)
            ·
              refine ⟨5002452380027960619611081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53359492053631579942518197 5002452380027960619611081)
              ·
                refine ⟨3751839285020970464708311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5002452380027960619611081 3751839285020970464708311)
                ·
                  refine ⟨5627758927531455697062467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3751839285020970464708311 5627758927531455697062467)
                  ·
                    refine ⟨8441638391297183545593701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5627758927531455697062467 8441638391297183545593701)
                    ·
                      refine ⟨1582807198368221914798819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8441638391297183545593701 1582807198368221914798819)
                      ·
                        rfl

theorem cell23_3082506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_3082506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082506 prefixEnd_3082506 := by exact prefixLift 3082506
  have htrace : WordTrace (prefixWord ++ tailWord_3082506) baseStart_3082506 baseEnd_3082506 := by
    simpa [prefixWord, tailWord_3082506, baseEnd_3082506] using wordTrace_append hprefix tailTrace_3082506
  have hstable : (prefixWord ++ tailWord_3082506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082506).length < 2 ^ (prefixWord ++ tailWord_3082506).sum := by decide
  have hdescent : baseEnd_3082506 < baseStart_3082506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082519 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3082519 : Nat := 118140960795 + 3082519 * 2 ^ 59
def prefixEnd_3082519 : Nat := 4983230072969 + 3 ^ 40 * 3082519 * 2
def baseEnd_3082519 : Nat := 1582813873616730363936259

theorem tailTrace_3082519 : CollatzResearch.WordTrace tailWord_3082519 prefixEnd_3082519 1582813873616730363936259 := by
  unfold tailWord_3082519
  simp only [CollatzResearch.WordTrace]
  refine ⟨112428704319567590177298611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74952469546378393451532407 112428704319567590177298611)
  ·
    refine ⟨168643056479351385265947917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112428704319567590177298611 168643056479351385265947917)
    ·
      refine ⟨63241146179756769474730469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168643056479351385265947917 63241146179756769474730469)
      ·
        refine ⟨11857714908704394276511963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63241146179756769474730469 11857714908704394276511963)
        ·
          refine ⟨17786572363056591414767945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11857714908704394276511963 17786572363056591414767945)
          ·
            refine ⟨13339929272292443561075959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17786572363056591414767945 13339929272292443561075959)
            ·
              refine ⟨20009893908438665341613939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13339929272292443561075959 20009893908438665341613939)
              ·
                refine ⟨30014840862657998012420909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20009893908438665341613939 30014840862657998012420909)
                ·
                  refine ⟨11255565323496749254657841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30014840862657998012420909 11255565323496749254657841)
                  ·
                    refine ⟨8441673992622561940993381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11255565323496749254657841 8441673992622561940993381)
                    ·
                      refine ⟨1582813873616730363936259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8441673992622561940993381 1582813873616730363936259)
                      ·
                        rfl

theorem cell23_3082519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3082519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082519 prefixEnd_3082519 := by exact prefixLift 3082519
  have htrace : WordTrace (prefixWord ++ tailWord_3082519) baseStart_3082519 baseEnd_3082519 := by
    simpa [prefixWord, tailWord_3082519, baseEnd_3082519] using wordTrace_append hprefix tailTrace_3082519
  have hstable : (prefixWord ++ tailWord_3082519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082519).length < 2 ^ (prefixWord ++ tailWord_3082519).sum := by decide
  have hdescent : baseEnd_3082519 < baseStart_3082519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082533 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_3082533 : Nat := 118140960795 + 3082533 * 2 ^ 59
def prefixEnd_3082533 : Nat := 4983230072969 + 3 ^ 40 * 3082533 * 2
def baseEnd_3082533 : Nat := 527607020781964436387065

theorem tailTrace_3082533 : CollatzResearch.WordTrace tailWord_3082533 prefixEnd_3082533 527607020781964436387065 := by
  unfold tailWord_3082533
  simp only [CollatzResearch.WordTrace]
  refine ⟨112429214941516870568308253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74952809961011247045538835 112429214941516870568308253)
  ·
    refine ⟨42160955603068826463115595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112429214941516870568308253 42160955603068826463115595)
    ·
      refine ⟨63241433404603239694673393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42160955603068826463115595 63241433404603239694673393)
      ·
        refine ⟨47431075053452429771005045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63241433404603239694673393 47431075053452429771005045)
        ·
          refine ⟨4446663286261165291031723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47431075053452429771005045 4446663286261165291031723)
          ·
            refine ⟨6669994929391747936547585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446663286261165291031723 6669994929391747936547585)
            ·
              refine ⟨5002496197043810952410689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6669994929391747936547585 5002496197043810952410689)
              ·
                refine ⟨3751872147782858214308017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5002496197043810952410689 3751872147782858214308017)
                ·
                  refine ⟨2813904110837143660731013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3751872147782858214308017 2813904110837143660731013)
                  ·
                    refine ⟨527607020781964436387065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813904110837143660731013 527607020781964436387065)
                    ·
                      rfl

theorem cell23_3082533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_3082533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082533 prefixEnd_3082533 := by exact prefixLift 3082533
  have htrace : WordTrace (prefixWord ++ tailWord_3082533) baseStart_3082533 baseEnd_3082533 := by
    simpa [prefixWord, tailWord_3082533, baseEnd_3082533] using wordTrace_append hprefix tailTrace_3082533
  have hstable : (prefixWord ++ tailWord_3082533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082533).length < 2 ^ (prefixWord ++ tailWord_3082533).sum := by decide
  have hdescent : baseEnd_3082533 < baseStart_3082533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082546 : List Nat := [3, 2, 1, 1, 5, 2, 1, 8]
def baseStart_3082546 : Nat := 118140960795 + 3082546 * 2 ^ 59
def prefixEnd_3082546 : Nat := 4983230072969 + 3 ^ 40 * 3082546 * 2
def baseEnd_3082546 : Nat := 58623249540533398455505

theorem tailTrace_3082546 : CollatzResearch.WordTrace tailWord_3082546 prefixEnd_3082546 58623249540533398455505 := by
  unfold tailWord_3082546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28107422272617443447132873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74953126060313182525687661 28107422272617443447132873)
  ·
    refine ⟨21080566704463082585349655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28107422272617443447132873 21080566704463082585349655)
    ·
      refine ⟨31620850056694623878024483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21080566704463082585349655 31620850056694623878024483)
      ·
        refine ⟨47431275085041935817036725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31620850056694623878024483 47431275085041935817036725)
        ·
          refine ⟨4446682039222681482847193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47431275085041935817036725 4446682039222681482847193)
          ·
            refine ⟨3335011529417011112135395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4446682039222681482847193 3335011529417011112135395)
            ·
              refine ⟨5002517294125516668203093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335011529417011112135395 5002517294125516668203093)
              ·
                refine ⟨58623249540533398455505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5002517294125516668203093 58623249540533398455505)
                ·
                  rfl

theorem cell23_3082546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 8].length) (baseStart_3082546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082546 prefixEnd_3082546 := by exact prefixLift 3082546
  have htrace : WordTrace (prefixWord ++ tailWord_3082546) baseStart_3082546 baseEnd_3082546 := by
    simpa [prefixWord, tailWord_3082546, baseEnd_3082546] using wordTrace_append hprefix tailTrace_3082546
  have hstable : (prefixWord ++ tailWord_3082546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082546).length < 2 ^ (prefixWord ++ tailWord_3082546).sum := by decide
  have hdescent : baseEnd_3082546 < baseStart_3082546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082556 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_3082556 : Nat := 118140960795 + 3082556 * 2 ^ 59
def prefixEnd_3082556 : Nat := 4983230072969 + 3 ^ 40 * 3082556 * 2
def baseEnd_3082556 : Nat := 1582832872400946719173589

theorem tailTrace_3082556 : CollatzResearch.WordTrace tailWord_3082556 prefixEnd_3082556 1582832872400946719173589 := by
  unfold tailWord_3082556
  simp only [CollatzResearch.WordTrace]
  refine ⟨56215026910216772748197761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74953369213622363664263681 56215026910216772748197761)
  ·
    refine ⟨42161270182662579561148321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56215026910216772748197761 42161270182662579561148321)
    ·
      refine ⟨31620952636996934670861241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42161270182662579561148321 31620952636996934670861241)
      ·
        refine ⟨23715714477747701003145931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31620952636996934670861241 23715714477747701003145931)
        ·
          refine ⟨35573571716621551504718897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23715714477747701003145931 35573571716621551504718897)
          ·
            refine ⟨26680178787466163628539173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35573571716621551504718897 26680178787466163628539173)
            ·
              refine ⟨5002533522649905680351095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26680178787466163628539173 5002533522649905680351095)
              ·
                refine ⟨7503800283974858520526643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002533522649905680351095 7503800283974858520526643)
                ·
                  refine ⟨11255700425962287780789965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7503800283974858520526643 11255700425962287780789965)
                  ·
                    refine ⟨4220887659735857917796237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11255700425962287780789965 4220887659735857917796237)
                    ·
                      refine ⟨1582832872400946719173589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4220887659735857917796237 1582832872400946719173589)
                      ·
                        rfl

theorem cell23_3082556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_3082556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082556 prefixEnd_3082556 := by exact prefixLift 3082556
  have htrace : WordTrace (prefixWord ++ tailWord_3082556) baseStart_3082556 baseEnd_3082556 := by
    simpa [prefixWord, tailWord_3082556, baseEnd_3082556] using wordTrace_append hprefix tailTrace_3082556
  have hstable : (prefixWord ++ tailWord_3082556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082556).length < 2 ^ (prefixWord ++ tailWord_3082556).sum := by decide
  have hdescent : baseEnd_3082556 < baseStart_3082556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082583 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 1, 3, 2]
def baseStart_3082583 : Nat := 118140960795 + 3082583 * 2 ^ 59
def prefixEnd_3082583 : Nat := 4983230072969 + 3 ^ 40 * 3082583 * 2
def baseEnd_3082583 : Nat := 1582846736378618113535965

theorem tailTrace_3082583 : CollatzResearch.WordTrace tailWord_3082583 prefixEnd_3082583 1582846736378618113535965 := by
  unfold tailWord_3082583
  simp only [CollatzResearch.WordTrace]
  refine ⟨112431038591335729107628403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74954025727557152738418935 112431038591335729107628403)
  ·
    refine ⟨168646557887003593661442605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112431038591335729107628403 168646557887003593661442605)
    ·
      refine ⟨63242459207626347623040977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168646557887003593661442605 63242459207626347623040977)
      ·
        refine ⟨47431844405719760717280733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63242459207626347623040977 47431844405719760717280733)
        ·
          refine ⟨17786941652144910268980275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47431844405719760717280733 17786941652144910268980275)
          ·
            refine ⟨26680412478217365403470413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17786941652144910268980275 26680412478217365403470413)
            ·
              refine ⟨10005154679331512026301405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26680412478217365403470413 10005154679331512026301405)
              ·
                refine ⟨3751933004749317009863027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10005154679331512026301405 3751933004749317009863027)
                ·
                  refine ⟨5627899507123975514794541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3751933004749317009863027 5627899507123975514794541)
                  ·
                    refine ⟨2110462315171490818047953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5627899507123975514794541 2110462315171490818047953)
                    ·
                      refine ⟨1582846736378618113535965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110462315171490818047953 1582846736378618113535965)
                      ·
                        rfl

theorem cell23_3082583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_3082583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082583 prefixEnd_3082583 := by exact prefixLift 3082583
  have htrace : WordTrace (prefixWord ++ tailWord_3082583) baseStart_3082583 baseEnd_3082583 := by
    simpa [prefixWord, tailWord_3082583, baseEnd_3082583] using wordTrace_append hprefix tailTrace_3082583
  have hstable : (prefixWord ++ tailWord_3082583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082583).length < 2 ^ (prefixWord ++ tailWord_3082583).sum := by decide
  have hdescent : baseEnd_3082583 < baseStart_3082583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082619 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 7]
def baseStart_3082619 : Nat := 118140960795 + 3082619 * 2 ^ 59
def prefixEnd_3082619 : Nat := 4983230072969 + 3 ^ 40 * 3082619 * 2
def baseEnd_3082619 : Nat := 175873913520242219187311

theorem tailTrace_3082619 : CollatzResearch.WordTrace tailWord_3082619 prefixEnd_3082619 175873913520242219187311 := by
  unfold tailWord_3082619
  simp only [CollatzResearch.WordTrace]
  refine ⟨112432351619205307255938911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74954901079470204837292607 112432351619205307255938911)
  ·
    refine ⟨168648527428807960883908367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112432351619205307255938911 168648527428807960883908367)
    ·
      refine ⟨252972791143211941325862551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168648527428807960883908367 252972791143211941325862551)
      ·
        refine ⟨379459186714817911988793827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252972791143211941325862551 379459186714817911988793827)
        ·
          refine ⟨569188780072226867983190741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379459186714817911988793827 569188780072226867983190741)
          ·
            refine ⟨13340362032942817218356033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 569188780072226867983190741 13340362032942817218356033)
            ·
              refine ⟨10005271524707112913767025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13340362032942817218356033 10005271524707112913767025)
              ·
                refine ⟨7503953643530334685325269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10005271524707112913767025 7503953643530334685325269)
                ·
                  refine ⟨175873913520242219187311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7503953643530334685325269 175873913520242219187311)
                  ·
                    rfl

theorem cell23_3082619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 7].length) (baseStart_3082619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082619 prefixEnd_3082619 := by exact prefixLift 3082619
  have htrace : WordTrace (prefixWord ++ tailWord_3082619) baseStart_3082619 baseEnd_3082619 := by
    simpa [prefixWord, tailWord_3082619, baseEnd_3082619] using wordTrace_append hprefix tailTrace_3082619
  have hstable : (prefixWord ++ tailWord_3082619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082619).length < 2 ^ (prefixWord ++ tailWord_3082619).sum := by decide
  have hdescent : baseEnd_3082619 < baseStart_3082619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082653 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 7]
def baseStart_3082653 : Nat := 118140960795 + 3082653 * 2 ^ 59
def prefixEnd_3082653 : Nat := 4983230072969 + 3 ^ 40 * 3082653 * 2
def baseEnd_3082653 : Nat := 175875853336048093295627

theorem tailTrace_3082653 : CollatzResearch.WordTrace tailWord_3082653 prefixEnd_3082653 175875853336048093295627 := by
  unfold tailWord_3082653
  simp only [CollatzResearch.WordTrace]
  refine ⟨112433591701082131062676613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74955727800721420708451075 112433591701082131062676613)
  ·
    refine ⟨21081298443952899574251865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112433591701082131062676613 21081298443952899574251865)
    ·
      refine ⟨15810973832964674680688899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21081298443952899574251865 15810973832964674680688899)
      ·
        refine ⟨23716460749447012021033349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15810973832964674680688899 23716460749447012021033349)
        ·
          refine ⟨4446836390521314753943753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23716460749447012021033349 4446836390521314753943753)
          ·
            refine ⟨3335127292890986065457815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4446836390521314753943753 3335127292890986065457815)
            ·
              refine ⟨5002690939336479098186723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335127292890986065457815 5002690939336479098186723)
              ·
                refine ⟨7504036409004718647280085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002690939336479098186723 7504036409004718647280085)
                ·
                  refine ⟨175875853336048093295627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7504036409004718647280085 175875853336048093295627)
                  ·
                    rfl

theorem cell23_3082653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_3082653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082653 prefixEnd_3082653 := by exact prefixLift 3082653
  have htrace : WordTrace (prefixWord ++ tailWord_3082653) baseStart_3082653 baseEnd_3082653 := by
    simpa [prefixWord, tailWord_3082653, baseEnd_3082653] using wordTrace_append hprefix tailTrace_3082653
  have hstable : (prefixWord ++ tailWord_3082653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082653).length < 2 ^ (prefixWord ++ tailWord_3082653).sum := by decide
  have hdescent : baseEnd_3082653 < baseStart_3082653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082659 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 7]
def baseStart_3082659 : Nat := 118140960795 + 3082659 * 2 ^ 59
def prefixEnd_3082659 : Nat := 4983230072969 + 3 ^ 40 * 3082659 * 2
def baseEnd_3082659 : Nat := 1582885760908359816185615

theorem tailTrace_3082659 : CollatzResearch.WordTrace tailWord_3082659 prefixEnd_3082659 1582885760908359816185615 := by
  unfold tailWord_3082659
  simp only [CollatzResearch.WordTrace]
  refine ⟨112433810539060394087395031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74955873692706929391596687 112433810539060394087395031)
  ·
    refine ⟨168650715808590591131092547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112433810539060394087395031 168650715808590591131092547)
    ·
      refine ⟨252976073712885886696638821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168650715808590591131092547 252976073712885886696638821)
      ·
        refine ⟨47433013821166103755619779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252976073712885886696638821 47433013821166103755619779)
        ·
          refine ⟨71149520731749155633429669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47433013821166103755619779 71149520731749155633429669)
          ·
            refine ⟨13340535137202966681268063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71149520731749155633429669 13340535137202966681268063)
            ·
              refine ⟨20010802705804450021902095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13340535137202966681268063 20010802705804450021902095)
              ·
                refine ⟨30016204058706675032853143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20010802705804450021902095 30016204058706675032853143)
                ·
                  refine ⟨45024306088060012549279715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30016204058706675032853143 45024306088060012549279715)
                  ·
                    refine ⟨67536459132090018823919573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45024306088060012549279715 67536459132090018823919573)
                    ·
                      refine ⟨1582885760908359816185615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67536459132090018823919573 1582885760908359816185615)
                      ·
                        rfl

theorem cell23_3082659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_3082659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082659 prefixEnd_3082659 := by exact prefixLift 3082659
  have htrace : WordTrace (prefixWord ++ tailWord_3082659) baseStart_3082659 baseEnd_3082659 := by
    simpa [prefixWord, tailWord_3082659, baseEnd_3082659] using wordTrace_append hprefix tailTrace_3082659
  have hstable : (prefixWord ++ tailWord_3082659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082659).length < 2 ^ (prefixWord ++ tailWord_3082659).sum := by decide
  have hdescent : baseEnd_3082659 < baseStart_3082659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082664 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3082664 : Nat := 118140960795 + 3082664 * 2 ^ 59
def prefixEnd_3082664 : Nat := 4983230072969 + 3 ^ 40 * 3082664 * 2
def baseEnd_3082664 : Nat := 1582888328311632296623093

theorem tailTrace_3082664 : CollatzResearch.WordTrace tailWord_3082664 prefixEnd_3082664 1582888328311632296623093 := by
  unfold tailWord_3082664
  simp only [CollatzResearch.WordTrace]
  refine ⟨56216996452021139970663523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74955995269361519960884697 56216996452021139970663523)
  ·
    refine ⟨84325494678031709955995285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56216996452021139970663523 84325494678031709955995285)
    ·
      refine ⟨3952757563032736404187279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84325494678031709955995285 3952757563032736404187279)
      ·
        refine ⟨5929136344549104606280919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3952757563032736404187279 5929136344549104606280919)
        ·
          refine ⟨8893704516823656909421379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5929136344549104606280919 8893704516823656909421379)
          ·
            refine ⟨13340556775235485364132069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8893704516823656909421379 13340556775235485364132069)
            ·
              refine ⟨2501354395356653505774763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13340556775235485364132069 2501354395356653505774763)
              ·
                refine ⟨3752031593034980258662145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501354395356653505774763 3752031593034980258662145)
                ·
                  refine ⟨2814023694776235193996609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3752031593034980258662145 2814023694776235193996609)
                  ·
                    refine ⟨2110517771082176395497457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2814023694776235193996609 2110517771082176395497457)
                    ·
                      refine ⟨1582888328311632296623093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110517771082176395497457 1582888328311632296623093)
                      ·
                        rfl

theorem cell23_3082664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3082664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082664 prefixEnd_3082664 := by exact prefixLift 3082664
  have htrace : WordTrace (prefixWord ++ tailWord_3082664) baseStart_3082664 baseEnd_3082664 := by
    simpa [prefixWord, tailWord_3082664, baseEnd_3082664] using wordTrace_append hprefix tailTrace_3082664
  have hstable : (prefixWord ++ tailWord_3082664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082664).length < 2 ^ (prefixWord ++ tailWord_3082664).sum := by decide
  have hdescent : baseEnd_3082664 < baseStart_3082664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082686 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3082686 : Nat := 118140960795 + 3082686 * 2 ^ 59
def prefixEnd_3082686 : Nat := 4983230072969 + 3 ^ 40 * 3082686 * 2
def baseEnd_3082686 : Nat := 1582899624886031210547991

theorem tailTrace_3082686 : CollatzResearch.WordTrace tailWord_3082686 prefixEnd_3082686 1582899624886031210547991 := by
  unfold tailWord_3082686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14054349413745322212328489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74956530206641718465751941 14054349413745322212328489)
  ·
    refine ⟨10540762060308991659246367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14054349413745322212328489 10540762060308991659246367)
    ·
      refine ⟨15811143090463487488869551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10540762060308991659246367 15811143090463487488869551)
      ·
        refine ⟨23716714635695231233304327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15811143090463487488869551 23716714635695231233304327)
        ·
          refine ⟨35575071953542846849956491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23716714635695231233304327 35575071953542846849956491)
          ·
            refine ⟨53362607930314270274934737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35575071953542846849956491 53362607930314270274934737)
            ·
              refine ⟨40021955947735702706201053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53362607930314270274934737 40021955947735702706201053)
              ·
                refine ⟨15008233480400888514825395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40021955947735702706201053 15008233480400888514825395)
                ·
                  refine ⟨22512350220601332772238093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15008233480400888514825395 22512350220601332772238093)
                  ·
                    refine ⟨8442131332725499789589285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22512350220601332772238093 8442131332725499789589285)
                    ·
                      refine ⟨1582899624886031210547991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8442131332725499789589285 1582899624886031210547991)
                      ·
                        rfl

theorem cell23_3082686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3082686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082686 prefixEnd_3082686 := by exact prefixLift 3082686
  have htrace : WordTrace (prefixWord ++ tailWord_3082686) baseStart_3082686 baseEnd_3082686 := by
    simpa [prefixWord, tailWord_3082686, baseEnd_3082686] using wordTrace_append hprefix tailTrace_3082686
  have hstable : (prefixWord ++ tailWord_3082686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082686).length < 2 ^ (prefixWord ++ tailWord_3082686).sum := by decide
  have hdescent : baseEnd_3082686 < baseStart_3082686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082699 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 6]
def baseStart_3082699 : Nat := 118140960795 + 3082699 * 2 ^ 59
def prefixEnd_3082699 : Nat := 4983230072969 + 3 ^ 40 * 3082699 * 2
def baseEnd_3082699 : Nat := 1582906300134539659685431

theorem tailTrace_3082699 : CollatzResearch.WordTrace tailWord_3082699 prefixEnd_3082699 1582906300134539659685431 := by
  unfold tailWord_3082699
  simp only [CollatzResearch.WordTrace]
  refine ⟨112435269458915480918851151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74956846305943653945900767 112435269458915480918851151)
  ·
    refine ⟨168652904188373221378276727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112435269458915480918851151 168652904188373221378276727)
    ·
      refine ⟨252979356282559832067415091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168652904188373221378276727 252979356282559832067415091)
      ·
        refine ⟨379469034423839748101122637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252979356282559832067415091 379469034423839748101122637)
        ·
          refine ⟨142300887908939905537920989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379469034423839748101122637 142300887908939905537920989)
          ·
            refine ⟨53362832965852464576720371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142300887908939905537920989 53362832965852464576720371)
            ·
              refine ⟨80044249448778696865080557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53362832965852464576720371 80044249448778696865080557)
              ·
                refine ⟨30016593543292011324405209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80044249448778696865080557 30016593543292011324405209)
                ·
                  refine ⟨22512445157469008493303907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30016593543292011324405209 22512445157469008493303907)
                  ·
                    refine ⟨33768667736203512739955861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22512445157469008493303907 33768667736203512739955861)
                    ·
                      refine ⟨1582906300134539659685431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33768667736203512739955861 1582906300134539659685431)
                      ·
                        rfl

theorem cell23_3082699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_3082699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082699 prefixEnd_3082699 := by exact prefixLift 3082699
  have htrace : WordTrace (prefixWord ++ tailWord_3082699) baseStart_3082699 baseEnd_3082699 := by
    simpa [prefixWord, tailWord_3082699, baseEnd_3082699] using wordTrace_append hprefix tailTrace_3082699
  have hstable : (prefixWord ++ tailWord_3082699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082699).length < 2 ^ (prefixWord ++ tailWord_3082699).sum := by decide
  have hdescent : baseEnd_3082699 < baseStart_3082699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082729 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_3082729 : Nat := 118140960795 + 3082729 * 2 ^ 59
def prefixEnd_3082729 : Nat := 4983230072969 + 3 ^ 40 * 3082729 * 2
def baseEnd_3082729 : Nat := 1582921704554174542310293

theorem tailTrace_3082729 : CollatzResearch.WordTrace tailWord_3082729 prefixEnd_3082729 1582921704554174542310293 := by
  unfold tailWord_3082729
  simp only [CollatzResearch.WordTrace]
  refine ⟨112436363648806796042443241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74957575765871197361628827 112436363648806796042443241)
  ·
    refine ⟨84327272736605097031832431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112436363648806796042443241 84327272736605097031832431)
    ·
      refine ⟨126490909104907645547748647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84327272736605097031832431 126490909104907645547748647)
      ·
        refine ⟨189736363657361468321622971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126490909104907645547748647 189736363657361468321622971)
        ·
          refine ⟨284604545486042202482434457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189736363657361468321622971 284604545486042202482434457)
          ·
            refine ⟨213453409114531651861825843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284604545486042202482434457 213453409114531651861825843)
            ·
              refine ⟨320180113671797477792738765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213453409114531651861825843 320180113671797477792738765)
              ·
                refine ⟨120067542626924054172277037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320180113671797477792738765 120067542626924054172277037)
                ·
                  refine ⟨45025328485096520314603889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120067542626924054172277037 45025328485096520314603889)
                  ·
                    refine ⟨33768996363822390235952917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45025328485096520314603889 33768996363822390235952917)
                    ·
                      refine ⟨1582921704554174542310293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33768996363822390235952917 1582921704554174542310293)
                      ·
                        rfl

theorem cell23_3082729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_3082729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082729 prefixEnd_3082729 := by exact prefixLift 3082729
  have htrace : WordTrace (prefixWord ++ tailWord_3082729) baseStart_3082729 baseEnd_3082729 := by
    simpa [prefixWord, tailWord_3082729, baseEnd_3082729] using wordTrace_append hprefix tailTrace_3082729
  have hstable : (prefixWord ++ tailWord_3082729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082729).length < 2 ^ (prefixWord ++ tailWord_3082729).sum := by decide
  have hdescent : baseEnd_3082729 < baseStart_3082729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082796 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_3082796 : Nat := 118140960795 + 3082796 * 2 ^ 59
def prefixEnd_3082796 : Nat := 4983230072969 + 3 ^ 40 * 3082796 * 2
def baseEnd_3082796 : Nat := 1582956107758025780172485

theorem tailTrace_3082796 : CollatzResearch.WordTrace tailWord_3082796 prefixEnd_3082796 1582956107758025780172485 := by
  unfold tailWord_3082796
  simp only [CollatzResearch.WordTrace]
  refine ⟨56219403669782033242566121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74959204893042710990088161 56219403669782033242566121)
  ·
    refine ⟨42164552752336524931924591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56219403669782033242566121 42164552752336524931924591)
    ·
      refine ⟨63246829128504787397886887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42164552752336524931924591 63246829128504787397886887)
      ·
        refine ⟨94870243692757181096830331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63246829128504787397886887 94870243692757181096830331)
        ·
          refine ⟨142305365539135771645245497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94870243692757181096830331 142305365539135771645245497)
          ·
            refine ⟨106729024154351828733934123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142305365539135771645245497 106729024154351828733934123)
            ·
              refine ⟨160093536231527743100901185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106729024154351828733934123 160093536231527743100901185)
              ·
                refine ⟨120070152173645807325675889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160093536231527743100901185 120070152173645807325675889)
                ·
                  refine ⟨90052614130234355494256917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120070152173645807325675889 90052614130234355494256917)
                  ·
                    refine ⟨4221216287354735413793293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90052614130234355494256917 4221216287354735413793293)
                    ·
                      refine ⟨1582956107758025780172485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4221216287354735413793293 1582956107758025780172485)
                      ·
                        rfl

theorem cell23_3082796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_3082796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082796 prefixEnd_3082796 := by exact prefixLift 3082796
  have htrace : WordTrace (prefixWord ++ tailWord_3082796) baseStart_3082796 baseEnd_3082796 := by
    simpa [prefixWord, tailWord_3082796, baseEnd_3082796] using wordTrace_append hprefix tailTrace_3082796
  have hstable : (prefixWord ++ tailWord_3082796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082796).length < 2 ^ (prefixWord ++ tailWord_3082796).sum := by decide
  have hdescent : baseEnd_3082796 < baseStart_3082796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082813 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3082813 : Nat := 118140960795 + 3082813 * 2 ^ 59
def prefixEnd_3082813 : Nat := 4983230072969 + 3 ^ 40 * 3082813 * 2
def baseEnd_3082813 : Nat := 1582964836929152213659907

theorem tailTrace_3082813 : CollatzResearch.WordTrace tailWord_3082813 prefixEnd_3082813 1582964836929152213659907 := by
  unfold tailWord_3082813
  simp only [CollatzResearch.WordTrace]
  refine ⟨112439427380502478388501093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74959618253668318925667395 112439427380502478388501093)
  ·
    refine ⟨21082392633844214697843955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112439427380502478388501093 21082392633844214697843955)
    ·
      refine ⟨31623588950766322046765933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21082392633844214697843955 31623588950766322046765933)
      ·
        refine ⟨11858845856537370767537225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31623588950766322046765933 11858845856537370767537225)
        ·
          refine ⟨8894134392403028075652919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11858845856537370767537225 8894134392403028075652919)
          ·
            refine ⟨13341201588604542113479379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8894134392403028075652919 13341201588604542113479379)
            ·
              refine ⟨20011802382906813170219069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13341201588604542113479379 20011802382906813170219069)
              ·
                refine ⟨7504425893590054938832151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20011802382906813170219069 7504425893590054938832151)
                ·
                  refine ⟨11256638840385082408248227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7504425893590054938832151 11256638840385082408248227)
                  ·
                    refine ⟨16884958260577623612372341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11256638840385082408248227 16884958260577623612372341)
                    ·
                      refine ⟨1582964836929152213659907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16884958260577623612372341 1582964836929152213659907)
                      ·
                        rfl

theorem cell23_3082813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3082813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082813 prefixEnd_3082813 := by exact prefixLift 3082813
  have htrace : WordTrace (prefixWord ++ tailWord_3082813) baseStart_3082813 baseEnd_3082813 := by
    simpa [prefixWord, tailWord_3082813, baseEnd_3082813] using wordTrace_append hprefix tailTrace_3082813
  have hstable : (prefixWord ++ tailWord_3082813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082813).length < 2 ^ (prefixWord ++ tailWord_3082813).sum := by decide
  have hdescent : baseEnd_3082813 < baseStart_3082813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082814 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3082814 : Nat := 118140960795 + 3082814 * 2 ^ 59
def prefixEnd_3082814 : Nat := 4983230072969 + 3 ^ 40 * 3082814 * 2
def baseEnd_3082814 : Nat := 1582965350409806709747403

theorem tailTrace_3082814 : CollatzResearch.WordTrace tailWord_3082814 prefixEnd_3082814 1582965350409806709747403 := by
  unfold tailWord_3082814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14054932981687356944910937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74959642568999237039524997 14054932981687356944910937)
  ·
    refine ⟨10541199736265517708683203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14054932981687356944910937 10541199736265517708683203)
    ·
      refine ⟨15811799604398276563024805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10541199736265517708683203 15811799604398276563024805)
      ·
        refine ⟨2964712425824676855567151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15811799604398276563024805 2964712425824676855567151)
        ·
          refine ⟨4447068638737015283350727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964712425824676855567151 4447068638737015283350727)
          ·
            refine ⟨6670602958105522925026091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4447068638737015283350727 6670602958105522925026091)
            ·
              refine ⟨10005904437158284387539137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6670602958105522925026091 10005904437158284387539137)
              ·
                refine ⟨7504428327868713290654353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10005904437158284387539137 7504428327868713290654353)
                ·
                  refine ⟨5628321245901534967990765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7504428327868713290654353 5628321245901534967990765)
                  ·
                    refine ⟨2110620467213075612996537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5628321245901534967990765 2110620467213075612996537)
                    ·
                      refine ⟨1582965350409806709747403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110620467213075612996537 1582965350409806709747403)
                      ·
                        rfl

theorem cell23_3082814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3082814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082814 prefixEnd_3082814 := by exact prefixLift 3082814
  have htrace : WordTrace (prefixWord ++ tailWord_3082814) baseStart_3082814 baseEnd_3082814 := by
    simpa [prefixWord, tailWord_3082814, baseEnd_3082814] using wordTrace_append hprefix tailTrace_3082814
  have hstable : (prefixWord ++ tailWord_3082814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082814).length < 2 ^ (prefixWord ++ tailWord_3082814).sum := by decide
  have hdescent : baseEnd_3082814 < baseStart_3082814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082827 : List Nat := [1, 1, 1, 1, 3, 1, 4, 6, 1, 2, 2]
def baseStart_3082827 : Nat := 118140960795 + 3082827 * 2 ^ 59
def prefixEnd_3082827 : Nat := 4983230072969 + 3 ^ 40 * 3082827 * 2
def baseEnd_3082827 : Nat := 1582972025658315158884843

theorem tailTrace_3082827 : CollatzResearch.WordTrace tailWord_3082827 prefixEnd_3082827 1582972025658315158884843 := by
  unfold tailWord_3082827
  simp only [CollatzResearch.WordTrace]
  refine ⟨112439938002451758779510735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74959958668301172519673823 112439938002451758779510735)
  ·
    refine ⟨168659907003677638169266103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112439938002451758779510735 168659907003677638169266103)
    ·
      refine ⟨252989860505516457253899155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168659907003677638169266103 252989860505516457253899155)
      ·
        refine ⟨379484790758274685880848733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252989860505516457253899155 379484790758274685880848733)
        ·
          refine ⟨142306796534353007205318275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379484790758274685880848733 142306796534353007205318275)
          ·
            refine ⟨213460194801529510807977413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142306796534353007205318275 213460194801529510807977413)
            ·
              refine ⟨40023786525286783276495765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213460194801529510807977413 40023786525286783276495765)
              ·
                refine ⟨1876114993372817966085739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40023786525286783276495765 1876114993372817966085739)
                ·
                  refine ⟨2814172490059226949128609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876114993372817966085739 2814172490059226949128609)
                  ·
                    refine ⟨2110629367544420211846457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2814172490059226949128609 2110629367544420211846457)
                    ·
                      refine ⟨1582972025658315158884843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110629367544420211846457 1582972025658315158884843)
                      ·
                        rfl

theorem cell23_3082827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 2, 2].length) (baseStart_3082827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082827 prefixEnd_3082827 := by exact prefixLift 3082827
  have htrace : WordTrace (prefixWord ++ tailWord_3082827) baseStart_3082827 baseEnd_3082827 := by
    simpa [prefixWord, tailWord_3082827, baseEnd_3082827] using wordTrace_append hprefix tailTrace_3082827
  have hstable : (prefixWord ++ tailWord_3082827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082827).length < 2 ^ (prefixWord ++ tailWord_3082827).sum := by decide
  have hdescent : baseEnd_3082827 < baseStart_3082827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082844 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_3082844 : Nat := 118140960795 + 3082844 * 2 ^ 59
def prefixEnd_3082844 : Nat := 4983230072969 + 3 ^ 40 * 3082844 * 2
def baseEnd_3082844 : Nat := 1582980754829441592372265

theorem tailTrace_3082844 : CollatzResearch.WordTrace tailWord_3082844 prefixEnd_3082844 1582980754829441592372265 := by
  unfold tailWord_3082844
  simp only [CollatzResearch.WordTrace]
  refine ⟨56220279021695085341439793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74960372028926780455253057 56220279021695085341439793)
  ·
    refine ⟨42165209266271314006079845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56220279021695085341439793 42165209266271314006079845)
    ·
      refine ⟨7905976737425871376139971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42165209266271314006079845 7905976737425871376139971)
      ·
        refine ⟨11858965106138807064209957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7905976737425871376139971 11858965106138807064209957)
        ·
          refine ⟨2223555957401026324539367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11858965106138807064209957 2223555957401026324539367)
          ·
            refine ⟨3335333936101539486809051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223555957401026324539367 3335333936101539486809051)
            ·
              refine ⟨5003000904152309230213577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335333936101539486809051 5003000904152309230213577)
              ·
                refine ⟨3752250678114231922660183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5003000904152309230213577 3752250678114231922660183)
                ·
                  refine ⟨5628376017171347883990275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752250678114231922660183 5628376017171347883990275)
                  ·
                    refine ⟨8442564025757021825985413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5628376017171347883990275 8442564025757021825985413)
                    ·
                      refine ⟨1582980754829441592372265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8442564025757021825985413 1582980754829441592372265)
                      ·
                        rfl

theorem cell23_3082844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_3082844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082844 prefixEnd_3082844 := by exact prefixLift 3082844
  have htrace : WordTrace (prefixWord ++ tailWord_3082844) baseStart_3082844 baseEnd_3082844 := by
    simpa [prefixWord, tailWord_3082844, baseEnd_3082844] using wordTrace_append hprefix tailTrace_3082844
  have hstable : (prefixWord ++ tailWord_3082844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082844).length < 2 ^ (prefixWord ++ tailWord_3082844).sum := by decide
  have hdescent : baseEnd_3082844 < baseStart_3082844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082903 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_3082903 : Nat := 118140960795 + 3082903 * 2 ^ 59
def prefixEnd_3082903 : Nat := 4983230072969 + 3 ^ 40 * 3082903 * 2
def baseEnd_3082903 : Nat := 1583011050188056861534493

theorem tailTrace_3082903 : CollatzResearch.WordTrace tailWord_3082903 prefixEnd_3082903 1583011050188056861534493 := by
  unfold tailWord_3082903
  simp only [CollatzResearch.WordTrace]
  refine ⟨112442709950176423759277363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74961806633450949172851575 112442709950176423759277363)
  ·
    refine ⟨168664064925264635638916045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112442709950176423759277363 168664064925264635638916045)
    ·
      refine ⟨63249024346974238364593517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168664064925264635638916045 63249024346974238364593517)
      ·
        refine ⟨23718384130115339386722569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63249024346974238364593517 23718384130115339386722569)
        ·
          refine ⟨17788788097586504540041927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23718384130115339386722569 17788788097586504540041927)
          ·
            refine ⟨26683182146379756810062891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17788788097586504540041927 26683182146379756810062891)
            ·
              refine ⟨40024773219569635215094337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26683182146379756810062891 40024773219569635215094337)
              ·
                refine ⟨30018579914677226411320753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40024773219569635215094337 30018579914677226411320753)
                ·
                  refine ⟨22513934936007919808490565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30018579914677226411320753 22513934936007919808490565)
                  ·
                    refine ⟨4221362800501484964091981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22513934936007919808490565 4221362800501484964091981)
                    ·
                      refine ⟨1583011050188056861534493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4221362800501484964091981 1583011050188056861534493)
                      ·
                        rfl

theorem cell23_3082903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_3082903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082903 prefixEnd_3082903 := by exact prefixLift 3082903
  have htrace : WordTrace (prefixWord ++ tailWord_3082903) baseStart_3082903 baseEnd_3082903 := by
    simpa [prefixWord, tailWord_3082903, baseEnd_3082903] using wordTrace_append hprefix tailTrace_3082903
  have hstable : (prefixWord ++ tailWord_3082903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082903).length < 2 ^ (prefixWord ++ tailWord_3082903).sum := by decide
  have hdescent : baseEnd_3082903 < baseStart_3082903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082940 : List Nat := [2, 2, 2, 3, 1, 1, 1, 6, 5]
def baseStart_3082940 : Nat := 118140960795 + 3082940 * 2 ^ 59
def prefixEnd_3082940 : Nat := 4983230072969 + 3 ^ 40 * 3082940 * 2
def baseEnd_3082940 : Nat := 175892227663585912974647

theorem tailTrace_3082940 : CollatzResearch.WordTrace tailWord_3082940 prefixEnd_3082940 175892227663585912974647 := by
  unfold tailWord_3082940
  simp only [CollatzResearch.WordTrace]
  refine ⟨56222029725521189539187137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74962706300694919385582849 56222029725521189539187137)
  ·
    refine ⟨42166522294140892154390353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56222029725521189539187137 42166522294140892154390353)
    ·
      refine ⟨31624891720605669115792765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42166522294140892154390353 31624891720605669115792765)
      ·
        refine ⟨11859334395227125918422287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31624891720605669115792765 11859334395227125918422287)
        ·
          refine ⟨17789001592840688877633431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11859334395227125918422287 17789001592840688877633431)
          ·
            refine ⟨26683502389261033316450147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17789001592840688877633431 26683502389261033316450147)
            ·
              refine ⟨40025253583891549974675221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26683502389261033316450147 40025253583891549974675221)
              ·
                refine ⟨1876183761744916405062901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40025253583891549974675221 1876183761744916405062901)
                ·
                  refine ⟨175892227663585912974647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1876183761744916405062901 175892227663585912974647)
                  ·
                    rfl

theorem cell23_3082940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_3082940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082940 prefixEnd_3082940 := by exact prefixLift 3082940
  have htrace : WordTrace (prefixWord ++ tailWord_3082940) baseStart_3082940 baseEnd_3082940 := by
    simpa [prefixWord, tailWord_3082940, baseEnd_3082940] using wordTrace_append hprefix tailTrace_3082940
  have hstable : (prefixWord ++ tailWord_3082940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082940).length < 2 ^ (prefixWord ++ tailWord_3082940).sum := by decide
  have hdescent : baseEnd_3082940 < baseStart_3082940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3082990 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3082990 : Nat := 118140960795 + 3082990 * 2 ^ 59
def prefixEnd_3082990 : Nat := 4983230072969 + 3 ^ 40 * 3082990 * 2
def baseEnd_3082990 : Nat := 1583055723004998021146593

theorem tailTrace_3082990 : CollatzResearch.WordTrace tailWord_3082990 prefixEnd_3082990 1583055723004998021146593 := by
  unfold tailWord_3082990
  simp only [CollatzResearch.WordTrace]
  refine ⟨14055735387607654702211803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74963922067240825078462949 14055735387607654702211803)
  ·
    refine ⟨21083603081411482053317705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14055735387607654702211803 21083603081411482053317705)
    ·
      refine ⟨15812702311058611539988279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21083603081411482053317705 15812702311058611539988279)
      ·
        refine ⟨23719053466587917309982419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15812702311058611539988279 23719053466587917309982419)
        ·
          refine ⟨35578580199881875964973629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23719053466587917309982419 35578580199881875964973629)
          ·
            refine ⟨13341967574955703486865111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35578580199881875964973629 13341967574955703486865111)
            ·
              refine ⟨20012951362433555230297667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13341967574955703486865111 20012951362433555230297667)
              ·
                refine ⟨30019427043650332845446501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20012951362433555230297667 30019427043650332845446501)
                ·
                  refine ⟨5628642570684437408521219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30019427043650332845446501 5628642570684437408521219)
                  ·
                    refine ⟨8442963856026656112781829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5628642570684437408521219 8442963856026656112781829)
                    ·
                      refine ⟨1583055723004998021146593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8442963856026656112781829 1583055723004998021146593)
                      ·
                        rfl

theorem cell23_3082990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3082990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3082990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3082990 prefixEnd_3082990 := by exact prefixLift 3082990
  have htrace : WordTrace (prefixWord ++ tailWord_3082990) baseStart_3082990 baseEnd_3082990 := by
    simpa [prefixWord, tailWord_3082990, baseEnd_3082990] using wordTrace_append hprefix tailTrace_3082990
  have hstable : (prefixWord ++ tailWord_3082990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3082990).length < 2 ^ (prefixWord ++ tailWord_3082990).sum := by decide
  have hdescent : baseEnd_3082990 < baseStart_3082990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3082990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083057 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 3]
def baseStart_3083057 : Nat := 118140960795 + 3083057 * 2 ^ 59
def prefixEnd_3083057 : Nat := 4983230072969 + 3 ^ 40 * 3083057 * 2
def baseEnd_3083057 : Nat := 1583090126208849259008785

theorem tailTrace_3083057 : CollatzResearch.WordTrace tailWord_3083057 prefixEnd_3083057 1583090126208849259008785 := by
  unfold tailWord_3083057
  simp only [CollatzResearch.WordTrace]
  refine ⟨112448326791618508060383425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74965551194412338706922283 112448326791618508060383425)
  ·
    refine ⟨84336245093713881045287569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112448326791618508060383425 84336245093713881045287569)
    ·
      refine ⟨63252183820285410783965677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84336245093713881045287569 63252183820285410783965677)
      ·
        refine ⟨23719568932607029043987129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63252183820285410783965677 23719568932607029043987129)
        ·
          refine ⟨17789676699455271782990347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23719568932607029043987129 17789676699455271782990347)
          ·
            refine ⟨26684515049182907674485521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17789676699455271782990347 26684515049182907674485521)
            ·
              refine ⟨20013386286887180755864141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26684515049182907674485521 20013386286887180755864141)
              ·
                refine ⟨7505019857582692783449053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20013386286887180755864141 7505019857582692783449053)
                ·
                  refine ⟨2814382446593509793793395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7505019857582692783449053 2814382446593509793793395)
                  ·
                    refine ⟨4221573669890264690690093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2814382446593509793793395 4221573669890264690690093)
                    ·
                      refine ⟨1583090126208849259008785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4221573669890264690690093 1583090126208849259008785)
                      ·
                        rfl

theorem cell23_3083057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_3083057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083057 prefixEnd_3083057 := by exact prefixLift 3083057
  have htrace : WordTrace (prefixWord ++ tailWord_3083057) baseStart_3083057 baseEnd_3083057 := by
    simpa [prefixWord, tailWord_3083057, baseEnd_3083057] using wordTrace_append hprefix tailTrace_3083057
  have hstable : (prefixWord ++ tailWord_3083057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083057).length < 2 ^ (prefixWord ++ tailWord_3083057).sum := by decide
  have hdescent : baseEnd_3083057 < baseStart_3083057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083078 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3083078 : Nat := 118140960795 + 3083078 * 2 ^ 59
def prefixEnd_3083078 : Nat := 4983230072969 + 3 ^ 40 * 3083078 * 2
def baseEnd_3083078 : Nat := 1583100909302593676846189

theorem tailTrace_3083078 : CollatzResearch.WordTrace tailWord_3083078 prefixEnd_3083078 1583100909302593676846189 := by
  unfold tailWord_3083078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514034147641950895215559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74966061816361619097931925 3514034147641950895215559)
  ·
    refine ⟨5271051221462926342823339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3514034147641950895215559 5271051221462926342823339)
    ·
      refine ⟨7906576832194389514235009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5271051221462926342823339 7906576832194389514235009)
      ·
        refine ⟨5929932624145792135676257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7906576832194389514235009 5929932624145792135676257)
        ·
          refine ⟨4447449468109344101757193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5929932624145792135676257 4447449468109344101757193)
          ·
            refine ⟨3335587101082008076317895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4447449468109344101757193 3335587101082008076317895)
            ·
              refine ⟨5003380651623012114476843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335587101082008076317895 5003380651623012114476843)
              ·
                refine ⟨7505070977434518171715265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5003380651623012114476843 7505070977434518171715265)
                ·
                  refine ⟨5628803233075888628786449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7505070977434518171715265 5628803233075888628786449)
                  ·
                    refine ⟨4221602424806916471589837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5628803233075888628786449 4221602424806916471589837)
                    ·
                      refine ⟨1583100909302593676846189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4221602424806916471589837 1583100909302593676846189)
                      ·
                        rfl

theorem cell23_3083078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3083078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083078 prefixEnd_3083078 := by exact prefixLift 3083078
  have htrace : WordTrace (prefixWord ++ tailWord_3083078) baseStart_3083078 baseEnd_3083078 := by
    simpa [prefixWord, tailWord_3083078, baseEnd_3083078] using wordTrace_append hprefix tailTrace_3083078
  have hstable : (prefixWord ++ tailWord_3083078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083078).length < 2 ^ (prefixWord ++ tailWord_3083078).sum := by decide
  have hdescent : baseEnd_3083078 < baseStart_3083078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083080 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3083080 : Nat := 118140960795 + 3083080 * 2 ^ 59
def prefixEnd_3083080 : Nat := 4983230072969 + 3 ^ 40 * 3083080 * 2
def baseEnd_3083080 : Nat := 1583101936263902669021179

theorem tailTrace_3083080 : CollatzResearch.WordTrace tailWord_3083080 prefixEnd_3083080 1583101936263902669021179 := by
  unfold tailWord_3083080
  simp only [CollatzResearch.WordTrace]
  refine ⟨56224582835267591494235347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74966110447023455325647129 56224582835267591494235347)
  ·
    refine ⟨84336874252901387241353021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56224582835267591494235347 84336874252901387241353021)
    ·
      refine ⟨31626327844838020215507383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84336874252901387241353021 31626327844838020215507383)
      ·
        refine ⟨47439491767257030323261075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31626327844838020215507383 47439491767257030323261075)
        ·
          refine ⟨71159237650885545484891613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47439491767257030323261075 71159237650885545484891613)
          ·
            refine ⟨26684714119082079556834355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71159237650885545484891613 26684714119082079556834355)
            ·
              refine ⟨40027071178623119335251533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26684714119082079556834355 40027071178623119335251533)
              ·
                refine ⟨15010151691983669750719325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40027071178623119335251533 15010151691983669750719325)
                ·
                  refine ⟨5628806884493876156519747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15010151691983669750719325 5628806884493876156519747)
                  ·
                    refine ⟨8443210326740814234779621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5628806884493876156519747 8443210326740814234779621)
                    ·
                      refine ⟨1583101936263902669021179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8443210326740814234779621 1583101936263902669021179)
                      ·
                        rfl

theorem cell23_3083080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3083080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083080 prefixEnd_3083080 := by exact prefixLift 3083080
  have htrace : WordTrace (prefixWord ++ tailWord_3083080) baseStart_3083080 baseEnd_3083080 := by
    simpa [prefixWord, tailWord_3083080, baseEnd_3083080] using wordTrace_append hprefix tailTrace_3083080
  have hstable : (prefixWord ++ tailWord_3083080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083080).length < 2 ^ (prefixWord ++ tailWord_3083080).sum := by decide
  have hdescent : baseEnd_3083080 < baseStart_3083080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083084 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 2, 3, 2]
def baseStart_3083084 : Nat := 118140960795 + 3083084 * 2 ^ 59
def prefixEnd_3083084 : Nat := 4983230072969 + 3 ^ 40 * 3083084 * 2
def baseEnd_3083084 : Nat := 1583103990186520653371161

theorem tailTrace_3083084 : CollatzResearch.WordTrace tailWord_3083084 prefixEnd_3083084 1583103990186520653371161 := by
  unfold tailWord_3083084
  simp only [CollatzResearch.WordTrace]
  refine ⟨56224655781260345835808153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74966207708347127781077537 56224655781260345835808153)
  ·
    refine ⟨42168491835945259376856115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56224655781260345835808153 42168491835945259376856115)
    ·
      refine ⟨63252737753917889065284173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42168491835945259376856115 63252737753917889065284173)
      ·
        refine ⟨23719776657719208399481565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63252737753917889065284173 23719776657719208399481565)
        ·
          refine ⟨8894916246644703149805587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23719776657719208399481565 8894916246644703149805587)
          ·
            refine ⟨13342374369967054724708381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8894916246644703149805587 13342374369967054724708381)
            ·
              refine ⟨5003390388737645521765643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13342374369967054724708381 5003390388737645521765643)
              ·
                refine ⟨7505085583106468282648465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5003390388737645521765643 7505085583106468282648465)
                ·
                  refine ⟨5628814187329851211986349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7505085583106468282648465 5628814187329851211986349)
                  ·
                    refine ⟨2110805320248694204494881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5628814187329851211986349 2110805320248694204494881)
                    ·
                      refine ⟨1583103990186520653371161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110805320248694204494881 1583103990186520653371161)
                      ·
                        rfl

theorem cell23_3083084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_3083084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083084 prefixEnd_3083084 := by exact prefixLift 3083084
  have htrace : WordTrace (prefixWord ++ tailWord_3083084) baseStart_3083084 baseEnd_3083084 := by
    simpa [prefixWord, tailWord_3083084, baseEnd_3083084] using wordTrace_append hprefix tailTrace_3083084
  have hstable : (prefixWord ++ tailWord_3083084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083084).length < 2 ^ (prefixWord ++ tailWord_3083084).sum := by decide
  have hdescent : baseEnd_3083084 < baseStart_3083084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083090 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3083090 : Nat := 118140960795 + 3083090 * 2 ^ 59
def prefixEnd_3083090 : Nat := 4983230072969 + 3 ^ 40 * 3083090 * 2
def baseEnd_3083090 : Nat := 527702357023482543298711

theorem tailTrace_3083090 : CollatzResearch.WordTrace tailWord_3083090 prefixEnd_3083090 527702357023482543298711 := by
  unfold tailWord_3083090
  simp only [CollatzResearch.WordTrace]
  refine ⟨28112382600124738674083681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74966353600332636464223149 28112382600124738674083681)
  ·
    refine ⟨21084286950093554005562761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28112382600124738674083681 21084286950093554005562761)
    ·
      refine ⟨15813215212570165504172071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21084286950093554005562761 15813215212570165504172071)
      ·
        refine ⟨23719822818855248256258107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15813215212570165504172071 23719822818855248256258107)
        ·
          refine ⟨35579734228282872384387161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23719822818855248256258107 35579734228282872384387161)
          ·
            refine ⟨26684800671212154288290371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35579734228282872384387161 26684800671212154288290371)
            ·
              refine ⟨40027201006818231432435557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26684800671212154288290371 40027201006818231432435557)
              ·
                refine ⟨7505100188778418393581667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40027201006818231432435557 7505100188778418393581667)
                ·
                  refine ⟨11257650283167627590372501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7505100188778418393581667 11257650283167627590372501)
                  ·
                    refine ⟨527702357023482543298711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11257650283167627590372501 527702357023482543298711)
                    ·
                      rfl

theorem cell23_3083090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3083090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083090 prefixEnd_3083090 := by exact prefixLift 3083090
  have htrace : WordTrace (prefixWord ++ tailWord_3083090) baseStart_3083090 baseEnd_3083090 := by
    simpa [prefixWord, tailWord_3083090, baseEnd_3083090] using wordTrace_append hprefix tailTrace_3083090
  have hstable : (prefixWord ++ tailWord_3083090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083090).length < 2 ^ (prefixWord ++ tailWord_3083090).sum := by decide
  have hdescent : baseEnd_3083090 < baseStart_3083090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083097 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 4]
def baseStart_3083097 : Nat := 118140960795 + 3083097 * 2 ^ 59
def prefixEnd_3083097 : Nat := 4983230072969 + 3 ^ 40 * 3083097 * 2
def baseEnd_3083097 : Nat := 1583110665435029102508601

theorem tailTrace_3083097 : CollatzResearch.WordTrace tailWord_3083097 prefixEnd_3083097 1583110665435029102508601 := by
  unfold tailWord_3083097
  simp only [CollatzResearch.WordTrace]
  refine ⟨112449785711473594891839545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74966523807649063261226363 112449785711473594891839545)
  ·
    refine ⟨84337339283605196168879659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112449785711473594891839545 84337339283605196168879659)
    ·
      refine ⟨126506008925407794253319489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84337339283605196168879659 126506008925407794253319489)
      ·
        refine ⟨94879506694055845689989617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126506008925407794253319489 94879506694055845689989617)
        ·
          refine ⟨71159630020541884267492213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94879506694055845689989617 71159630020541884267492213)
          ·
            refine ⟨6671215314425801650077395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71159630020541884267492213 6671215314425801650077395)
            ·
              refine ⟨10006822971638702475116093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6671215314425801650077395 10006822971638702475116093)
              ·
                refine ⟨3752558614364513428168535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10006822971638702475116093 3752558614364513428168535)
                ·
                  refine ⟨5628837921546770142252803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752558614364513428168535 5628837921546770142252803)
                  ·
                    refine ⟨8443256882320155213379205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5628837921546770142252803 8443256882320155213379205)
                    ·
                      refine ⟨1583110665435029102508601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8443256882320155213379205 1583110665435029102508601)
                      ·
                        rfl

theorem cell23_3083097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_3083097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083097 prefixEnd_3083097 := by exact prefixLift 3083097
  have htrace : WordTrace (prefixWord ++ tailWord_3083097) baseStart_3083097 baseEnd_3083097 := by
    simpa [prefixWord, tailWord_3083097, baseEnd_3083097] using wordTrace_append hprefix tailTrace_3083097
  have hstable : (prefixWord ++ tailWord_3083097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083097).length < 2 ^ (prefixWord ++ tailWord_3083097).sum := by decide
  have hdescent : baseEnd_3083097 < baseStart_3083097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083103 : List Nat := [1, 1, 2, 3, 1, 3, 12]
def baseStart_3083103 : Nat := 118140960795 + 3083103 * 2 ^ 59
def prefixEnd_3083103 : Nat := 4983230072969 + 3 ^ 40 * 3083103 * 2
def baseEnd_3083103 : Nat := 19544614152085877518933

theorem tailTrace_3083103 : CollatzResearch.WordTrace tailWord_3083103 prefixEnd_3083103 19544614152085877518933 := by
  unfold tailWord_3083103
  simp only [CollatzResearch.WordTrace]
  refine ⟨112450004549451857916557963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74966669699634571944371975 112450004549451857916557963)
  ·
    refine ⟨168675006824177786874836945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112450004549451857916557963 168675006824177786874836945)
    ·
      refine ⟨126506255118133340156127709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168675006824177786874836945 126506255118133340156127709)
      ·
        refine ⟨47439845669300002558547891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126506255118133340156127709 47439845669300002558547891)
        ·
          refine ⟨71159768503950003837821837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47439845669300002558547891 71159768503950003837821837)
          ·
            refine ⟨26684913188981251439183189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71159768503950003837821837 26684913188981251439183189)
            ·
              refine ⟨19544614152085877518933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 26684913188981251439183189 19544614152085877518933)
              ·
                rfl

theorem cell23_3083103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 12].length) (baseStart_3083103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083103 prefixEnd_3083103 := by exact prefixLift 3083103
  have htrace : WordTrace (prefixWord ++ tailWord_3083103) baseStart_3083103 baseEnd_3083103 := by
    simpa [prefixWord, tailWord_3083103, baseEnd_3083103] using wordTrace_append hprefix tailTrace_3083103
  have hstable : (prefixWord ++ tailWord_3083103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083103).length < 2 ^ (prefixWord ++ tailWord_3083103).sum := by decide
  have hdescent : baseEnd_3083103 < baseStart_3083103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083107 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 4, 4]
def baseStart_3083107 : Nat := 118140960795 + 3083107 * 2 ^ 59
def prefixEnd_3083107 : Nat := 4983230072969 + 3 ^ 40 * 3083107 * 2
def baseEnd_3083107 : Nat := 527705266747191354461185

theorem tailTrace_3083107 : CollatzResearch.WordTrace tailWord_3083107 prefixEnd_3083107 527705266747191354461185 := by
  unfold tailWord_3083107
  simp only [CollatzResearch.WordTrace]
  refine ⟨112450150441437366599703575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74966766960958244399802383 112450150441437366599703575)
  ·
    refine ⟨168675225662156049899555363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112450150441437366599703575 168675225662156049899555363)
    ·
      refine ⟨253012838493234074849333045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168675225662156049899555363 253012838493234074849333045)
      ·
        refine ⟨23719953608740694517124973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253012838493234074849333045 23719953608740694517124973)
        ·
          refine ⟨8894982603277760443921865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23719953608740694517124973 8894982603277760443921865)
          ·
            refine ⟨6671236952458320332941399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8894982603277760443921865 6671236952458320332941399)
            ·
              refine ⟨10006855428687480499412099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6671236952458320332941399 10006855428687480499412099)
              ·
                refine ⟨15010283143031220749118149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10006855428687480499412099 15010283143031220749118149)
                ·
                  refine ⟨2814428089318353890459653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15010283143031220749118149 2814428089318353890459653)
                  ·
                    refine ⟨527705266747191354461185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2814428089318353890459653 527705266747191354461185)
                    ·
                      rfl

theorem cell23_3083107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 4].length) (baseStart_3083107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083107 prefixEnd_3083107 := by exact prefixLift 3083107
  have htrace : WordTrace (prefixWord ++ tailWord_3083107) baseStart_3083107 baseEnd_3083107 := by
    simpa [prefixWord, tailWord_3083107, baseEnd_3083107] using wordTrace_append hprefix tailTrace_3083107
  have hstable : (prefixWord ++ tailWord_3083107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083107).length < 2 ^ (prefixWord ++ tailWord_3083107).sum := by decide
  have hdescent : baseEnd_3083107 < baseStart_3083107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083113 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_3083113 : Nat := 118140960795 + 3083113 * 2 ^ 59
def prefixEnd_3083113 : Nat := 4983230072969 + 3 ^ 40 * 3083113 * 2
def baseEnd_3083113 : Nat := 1583118881125501039908527

theorem tailTrace_3083113 : CollatzResearch.WordTrace tailWord_3083113 prefixEnd_3083113 1583118881125501039908527 := by
  unfold tailWord_3083113
  simp only [CollatzResearch.WordTrace]
  refine ⟨112450369279415629624421993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74966912852943753082947995 112450369279415629624421993)
  ·
    refine ⟨84337776959561722218316495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112450369279415629624421993 84337776959561722218316495)
    ·
      refine ⟨126506665439342583327474743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84337776959561722218316495 126506665439342583327474743)
      ·
        refine ⟨189759998159013874991212115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126506665439342583327474743 189759998159013874991212115)
        ·
          refine ⟨284639997238520812486818173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189759998159013874991212115 284639997238520812486818173)
          ·
            refine ⟨106739998964445304682556815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284639997238520812486818173 106739998964445304682556815)
            ·
              refine ⟨160109998446667957023835223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106739998964445304682556815 160109998446667957023835223)
              ·
                refine ⟨240164997670001935535752835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160109998446667957023835223 240164997670001935535752835)
                ·
                  refine ⟨360247496505002903303629253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240164997670001935535752835 360247496505002903303629253)
                  ·
                    refine ⟨67546405594688044369430485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360247496505002903303629253 67546405594688044369430485)
                    ·
                      refine ⟨1583118881125501039908527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67546405594688044369430485 1583118881125501039908527)
                      ·
                        rfl

theorem cell23_3083113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_3083113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083113 prefixEnd_3083113 := by exact prefixLift 3083113
  have htrace : WordTrace (prefixWord ++ tailWord_3083113) baseStart_3083113 baseEnd_3083113 := by
    simpa [prefixWord, tailWord_3083113, baseEnd_3083113] using wordTrace_append hprefix tailTrace_3083113
  have hstable : (prefixWord ++ tailWord_3083113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083113).length < 2 ^ (prefixWord ++ tailWord_3083113).sum := by decide
  have hdescent : baseEnd_3083113 < baseStart_3083113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083147 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 3]
def baseStart_3083147 : Nat := 118140960795 + 3083147 * 2 ^ 59
def prefixEnd_3083147 : Nat := 4983230072969 + 3 ^ 40 * 3083147 * 2
def baseEnd_3083147 : Nat := 1583136339467753906883371

theorem tailTrace_3083147 : CollatzResearch.WordTrace tailWord_3083147 prefixEnd_3083147 1583136339467753906883371 := by
  unfold tailWord_3083147
  simp only [CollatzResearch.WordTrace]
  refine ⟨112451609361292453431159695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74967739574194968954106463 112451609361292453431159695)
  ·
    refine ⟨168677414041938680146739543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112451609361292453431159695 168677414041938680146739543)
    ·
      refine ⟨253016121062908020220109315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168677414041938680146739543 253016121062908020220109315)
      ·
        refine ⟨379524181594362030330163973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253016121062908020220109315 379524181594362030330163973)
        ·
          refine ⟨71160784048942880686905745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 379524181594362030330163973 71160784048942880686905745)
          ·
            refine ⟨53370588036707160515179309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71160784048942880686905745 53370588036707160515179309)
            ·
              refine ⟨20013970513765185193192241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53370588036707160515179309 20013970513765185193192241)
              ·
                refine ⟨15010477885323888894894181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20013970513765185193192241 15010477885323888894894181)
                ·
                  refine ⟨2814464603498229167792659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15010477885323888894894181 2814464603498229167792659)
                  ·
                    refine ⟨4221696905247343751688989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2814464603498229167792659 4221696905247343751688989)
                    ·
                      refine ⟨1583136339467753906883371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4221696905247343751688989 1583136339467753906883371)
                      ·
                        rfl

theorem cell23_3083147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 3].length) (baseStart_3083147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083147 prefixEnd_3083147 := by exact prefixLift 3083147
  have htrace : WordTrace (prefixWord ++ tailWord_3083147) baseStart_3083147 baseEnd_3083147 := by
    simpa [prefixWord, tailWord_3083147, baseEnd_3083147] using wordTrace_append hprefix tailTrace_3083147
  have hstable : (prefixWord ++ tailWord_3083147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083147).length < 2 ^ (prefixWord ++ tailWord_3083147).sum := by decide
  have hdescent : baseEnd_3083147 < baseStart_3083147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083154 : List Nat := [3, 2, 3, 2, 3, 1, 9]
def baseStart_3083154 : Nat := 118140960795 + 3083154 * 2 ^ 59
def prefixEnd_3083154 : Nat := 4983230072969 + 3 ^ 40 * 3083154 * 2
def baseEnd_3083154 : Nat := 19544937454720189870319

theorem tailTrace_3083154 : CollatzResearch.WordTrace tailWord_3083154 prefixEnd_3083154 19544937454720189870319 := by
  unfold tailWord_3083154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28112966168066773406666129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74967909781511395751109677 28112966168066773406666129)
  ·
    refine ⟨21084724626050080054999597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28112966168066773406666129 21084724626050080054999597)
    ·
      refine ⟨7906771734768780020624849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21084724626050080054999597 7906771734768780020624849)
      ·
        refine ⟨5930078801076585015468637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7906771734768780020624849 5930078801076585015468637)
        ·
          refine ⟨2223779550403719380800739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5930078801076585015468637 2223779550403719380800739)
          ·
            refine ⟨3335669325605579071201109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223779550403719380800739 3335669325605579071201109)
            ·
              refine ⟨19544937454720189870319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3335669325605579071201109 19544937454720189870319)
              ·
                rfl

theorem cell23_3083154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 9].length) (baseStart_3083154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083154 prefixEnd_3083154 := by exact prefixLift 3083154
  have htrace : WordTrace (prefixWord ++ tailWord_3083154) baseStart_3083154 baseEnd_3083154 := by
    simpa [prefixWord, tailWord_3083154, baseEnd_3083154] using wordTrace_append hprefix tailTrace_3083154
  have hstable : (prefixWord ++ tailWord_3083154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083154).length < 2 ^ (prefixWord ++ tailWord_3083154).sum := by decide
  have hdescent : baseEnd_3083154 < baseStart_3083154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083208 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_3083208 : Nat := 118140960795 + 3083208 * 2 ^ 59
def prefixEnd_3083208 : Nat := 4983230072969 + 3 ^ 40 * 3083208 * 2
def baseEnd_3083208 : Nat := 1583167661787678168220591

theorem tailTrace_3083208 : CollatzResearch.WordTrace tailWord_3083208 prefixEnd_3083208 1583167661787678168220591 := by
  unfold tailWord_3083208
  simp only [CollatzResearch.WordTrace]
  refine ⟨56226917107035730424565139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74969222809380973899420185 56226917107035730424565139)
  ·
    refine ⟨84340375660553595636847709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56226917107035730424565139 84340375660553595636847709)
    ·
      refine ⟨31627640872707598363817891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84340375660553595636847709 31627640872707598363817891)
      ·
        refine ⟨47441461309061397545726837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31627640872707598363817891 47441461309061397545726837)
        ·
          refine ⟨4447636997724506019911891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47441461309061397545726837 4447636997724506019911891)
          ·
            refine ⟨6671455496586759029867837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4447636997724506019911891 6671455496586759029867837)
            ·
              refine ⟨2501795811220034636200439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6671455496586759029867837 2501795811220034636200439)
              ·
                refine ⟨3752693716830051954300659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501795811220034636200439 3752693716830051954300659)
                ·
                  refine ⟨5629040575245077931450989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752693716830051954300659 5629040575245077931450989)
                  ·
                    refine ⟨2110890215716904224294121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5629040575245077931450989 2110890215716904224294121)
                    ·
                      refine ⟨1583167661787678168220591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110890215716904224294121 1583167661787678168220591)
                      ·
                        rfl

theorem cell23_3083208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_3083208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083208 prefixEnd_3083208 := by exact prefixLift 3083208
  have htrace : WordTrace (prefixWord ++ tailWord_3083208) baseStart_3083208 baseEnd_3083208 := by
    simpa [prefixWord, tailWord_3083208, baseEnd_3083208] using wordTrace_append hprefix tailTrace_3083208
  have hstable : (prefixWord ++ tailWord_3083208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083208).length < 2 ^ (prefixWord ++ tailWord_3083208).sum := by decide
  have hdescent : baseEnd_3083208 < baseStart_3083208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083234 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3083234 : Nat := 118140960795 + 3083234 * 2 ^ 59
def prefixEnd_3083234 : Nat := 4983230072969 + 3 ^ 40 * 3083234 * 2
def baseEnd_3083234 : Nat := 1583181012284695066495471

theorem tailTrace_3083234 : CollatzResearch.WordTrace tailWord_3083234 prefixEnd_3083234 1583181012284695066495471 := by
  unfold tailWord_3083234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28113695627994316822394189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74969855007984844859717837 28113695627994316822394189)
  ·
    refine ⟨10542635860497868808397821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28113695627994316822394189 10542635860497868808397821)
    ·
      refine ⟨3953488447686700803149183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10542635860497868808397821 3953488447686700803149183)
      ·
        refine ⟨5930232671530051204723775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3953488447686700803149183 5930232671530051204723775)
        ·
          refine ⟨8895349007295076807085663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5930232671530051204723775 8895349007295076807085663)
          ·
            refine ⟨13343023510942615210628495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8895349007295076807085663 13343023510942615210628495)
            ·
              refine ⟨20014535266413922815942743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13343023510942615210628495 20014535266413922815942743)
              ·
                refine ⟨30021802899620884223914115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20014535266413922815942743 30021802899620884223914115)
                ·
                  refine ⟨45032704349431326335871173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30021802899620884223914115 45032704349431326335871173)
                  ·
                    refine ⟨8443632065518373687975845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45032704349431326335871173 8443632065518373687975845)
                    ·
                      refine ⟨1583181012284695066495471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8443632065518373687975845 1583181012284695066495471)
                      ·
                        rfl

theorem cell23_3083234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3083234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083234 prefixEnd_3083234 := by exact prefixLift 3083234
  have htrace : WordTrace (prefixWord ++ tailWord_3083234) baseStart_3083234 baseEnd_3083234 := by
    simpa [prefixWord, tailWord_3083234, baseEnd_3083234] using wordTrace_append hprefix tailTrace_3083234
  have hstable : (prefixWord ++ tailWord_3083234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083234).length < 2 ^ (prefixWord ++ tailWord_3083234).sum := by decide
  have hdescent : baseEnd_3083234 < baseStart_3083234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083314 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_3083314 : Nat := 118140960795 + 3083314 * 2 ^ 59
def prefixEnd_3083314 : Nat := 4983230072969 + 3 ^ 40 * 3083314 * 2
def baseEnd_3083314 : Nat := 1583222090737054753495103

theorem tailTrace_3083314 : CollatzResearch.WordTrace tailWord_3083314 prefixEnd_3083314 1583222090737054753495103 := by
  unfold tailWord_3083314
  simp only [CollatzResearch.WordTrace]
  refine ⟨28114425087921860238122249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74971800234458293968325997 28114425087921860238122249)
  ·
    refine ⟨21085818815941395178591687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28114425087921860238122249 21085818815941395178591687)
    ·
      refine ⟨31628728223912092767887531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21085818815941395178591687 31628728223912092767887531)
      ·
        refine ⟨47443092335868139151831297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31628728223912092767887531 47443092335868139151831297)
        ·
          refine ⟨35582319251901104363873473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47443092335868139151831297 35582319251901104363873473)
          ·
            refine ⟨26686739438925828272905105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35582319251901104363873473 26686739438925828272905105)
            ·
              refine ⟨20015054579194371204678829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26686739438925828272905105 20015054579194371204678829)
              ·
                refine ⟨7505645467197889201754561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20015054579194371204678829 7505645467197889201754561)
                ·
                  refine ⟨5629234100398416901315921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7505645467197889201754561 5629234100398416901315921)
                  ·
                    refine ⟨4221925575298812675986941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5629234100398416901315921 4221925575298812675986941)
                    ·
                      refine ⟨1583222090737054753495103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4221925575298812675986941 1583222090737054753495103)
                      ·
                        rfl

theorem cell23_3083314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_3083314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083314 prefixEnd_3083314 := by exact prefixLift 3083314
  have htrace : WordTrace (prefixWord ++ tailWord_3083314) baseStart_3083314 baseEnd_3083314 := by
    simpa [prefixWord, tailWord_3083314, baseEnd_3083314] using wordTrace_append hprefix tailTrace_3083314
  have hstable : (prefixWord ++ tailWord_3083314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083314).length < 2 ^ (prefixWord ++ tailWord_3083314).sum := by decide
  have hdescent : baseEnd_3083314 < baseStart_3083314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083354 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2]
def baseStart_3083354 : Nat := 118140960795 + 3083354 * 2 ^ 59
def prefixEnd_3083354 : Nat := 4983230072969 + 3 ^ 40 * 3083354 * 2
def baseEnd_3083354 : Nat := 1583242629963234596994919

theorem tailTrace_3083354 : CollatzResearch.WordTrace tailWord_3083354 prefixEnd_3083354 1583242629963234596994919 := by
  unfold tailWord_3083354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28114789817885631945986279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74972772847695018522630077 28114789817885631945986279)
  ·
    refine ⟨42172184726828447918979419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28114789817885631945986279 42172184726828447918979419)
    ·
      refine ⟨63258277090242671878469129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42172184726828447918979419 63258277090242671878469129)
      ·
        refine ⟨47443707817682003908851847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63258277090242671878469129 47443707817682003908851847)
        ·
          refine ⟨71165561726523005863277771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47443707817682003908851847 71165561726523005863277771)
          ·
            refine ⟨106748342589784508794916657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71165561726523005863277771 106748342589784508794916657)
            ·
              refine ⟨80061256942338381596187493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106748342589784508794916657 80061256942338381596187493)
              ·
                refine ⟨15011485676688446549285155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80061256942338381596187493 15011485676688446549285155)
                ·
                  refine ⟨22517228515032669823927733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15011485676688446549285155 22517228515032669823927733)
                  ·
                    refine ⟨2110990173284312795993225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22517228515032669823927733 2110990173284312795993225)
                    ·
                      refine ⟨1583242629963234596994919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2110990173284312795993225 1583242629963234596994919)
                      ·
                        rfl

theorem cell23_3083354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_3083354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083354 prefixEnd_3083354 := by exact prefixLift 3083354
  have htrace : WordTrace (prefixWord ++ tailWord_3083354) baseStart_3083354 baseEnd_3083354 := by
    simpa [prefixWord, tailWord_3083354, baseEnd_3083354] using wordTrace_append hprefix tailTrace_3083354
  have hstable : (prefixWord ++ tailWord_3083354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083354).length < 2 ^ (prefixWord ++ tailWord_3083354).sum := by decide
  have hdescent : baseEnd_3083354 < baseStart_3083354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083378 : List Nat := [3, 2, 1, 2, 2, 1, 2, 5, 1, 1, 3]
def baseStart_3083378 : Nat := 118140960795 + 3083378 * 2 ^ 59
def prefixEnd_3083378 : Nat := 4983230072969 + 3 ^ 40 * 3083378 * 2
def baseEnd_3083378 : Nat := 1583254953498942503094809

theorem tailTrace_3083378 : CollatzResearch.WordTrace tailWord_3083378 prefixEnd_3083378 1583254953498942503094809 := by
  unfold tailWord_3083378
  simp only [CollatzResearch.WordTrace]
  refine ⟨28115008655863894970704697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74973356415637053255212525 28115008655863894970704697)
  ·
    refine ⟨21086256491897921228028523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28115008655863894970704697 21086256491897921228028523)
    ·
      refine ⟨31629384737846881842042785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21086256491897921228028523 31629384737846881842042785)
      ·
        refine ⟨23722038553385161381532089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31629384737846881842042785 23722038553385161381532089)
        ·
          refine ⟨17791528915038871036149067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23722038553385161381532089 17791528915038871036149067)
          ·
            refine ⟨26687293372558306554223601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17791528915038871036149067 26687293372558306554223601)
            ·
              refine ⟨20015470029418729915667701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26687293372558306554223601 20015470029418729915667701)
              ·
                refine ⟨1876450315258005929593847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20015470029418729915667701 1876450315258005929593847)
                ·
                  refine ⟨2814675472887008894390771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876450315258005929593847 2814675472887008894390771)
                  ·
                    refine ⟨4222013209330513341586157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2814675472887008894390771 4222013209330513341586157)
                    ·
                      refine ⟨1583254953498942503094809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4222013209330513341586157 1583254953498942503094809)
                      ·
                        rfl

theorem cell23_3083378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_3083378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083378 prefixEnd_3083378 := by exact prefixLift 3083378
  have htrace : WordTrace (prefixWord ++ tailWord_3083378) baseStart_3083378 baseEnd_3083378 := by
    simpa [prefixWord, tailWord_3083378, baseEnd_3083378] using wordTrace_append hprefix tailTrace_3083378
  have hstable : (prefixWord ++ tailWord_3083378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083378).length < 2 ^ (prefixWord ++ tailWord_3083378).sum := by decide
  have hdescent : baseEnd_3083378 < baseStart_3083378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083384 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 1, 1, 4]
def baseStart_3083384 : Nat := 118140960795 + 3083384 * 2 ^ 59
def prefixEnd_3083384 : Nat := 4983230072969 + 3 ^ 40 * 3083384 * 2
def baseEnd_3083384 : Nat := 1583258034382869479619781

theorem tailTrace_3083384 : CollatzResearch.WordTrace tailWord_3083384 prefixEnd_3083384 1583258034382869479619781 := by
  unfold tailWord_3083384
  simp only [CollatzResearch.WordTrace]
  refine ⟨56230126730716921453768603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74973502307622561938358137 56230126730716921453768603)
  ·
    refine ⟨84345190096075382180652905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56230126730716921453768603 84345190096075382180652905)
    ·
      refine ⟨63258892572056536635489679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84345190096075382180652905 63258892572056536635489679)
      ·
        refine ⟨94888338858084804953234519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63258892572056536635489679 94888338858084804953234519)
        ·
          refine ⟨142332508287127207429851779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94888338858084804953234519 142332508287127207429851779)
          ·
            refine ⟨213498762430690811144777669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142332508287127207429851779 213498762430690811144777669)
            ·
              refine ⟨40031017955754527089645813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213498762430690811144777669 40031017955754527089645813)
              ·
                refine ⟨3752907933351986914654295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40031017955754527089645813 3752907933351986914654295)
                ·
                  refine ⟨5629361900027980371981443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752907933351986914654295 5629361900027980371981443)
                  ·
                    refine ⟨8444042850041970557972165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5629361900027980371981443 8444042850041970557972165)
                    ·
                      refine ⟨1583258034382869479619781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8444042850041970557972165 1583258034382869479619781)
                      ·
                        rfl

theorem cell23_3083384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_3083384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083384 prefixEnd_3083384 := by exact prefixLift 3083384
  have htrace : WordTrace (prefixWord ++ tailWord_3083384) baseStart_3083384 baseEnd_3083384 := by
    simpa [prefixWord, tailWord_3083384, baseEnd_3083384] using wordTrace_append hprefix tailTrace_3083384
  have hstable : (prefixWord ++ tailWord_3083384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083384).length < 2 ^ (prefixWord ++ tailWord_3083384).sum := by decide
  have hdescent : baseEnd_3083384 < baseStart_3083384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083418 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2]
def baseStart_3083418 : Nat := 118140960795 + 3083418 * 2 ^ 59
def prefixEnd_3083418 : Nat := 4983230072969 + 3 ^ 40 * 3083418 * 2
def baseEnd_3083418 : Nat := 1583275492725122346594625

theorem tailTrace_3083418 : CollatzResearch.WordTrace tailWord_3083418 prefixEnd_3083418 1583275492725122346594625 := by
  unfold tailWord_3083418
  simp only [CollatzResearch.WordTrace]
  refine ⟨28115373385827666678568727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74974329028873777809516605 28115373385827666678568727)
  ·
    refine ⟨42173060078741500017853091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28115373385827666678568727 42173060078741500017853091)
    ·
      refine ⟨63259590118112250026779637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42173060078741500017853091 63259590118112250026779637)
      ·
        refine ⟨5930586573573023440010591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63259590118112250026779637 5930586573573023440010591)
        ·
          refine ⟨8895879860359535160015887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5930586573573023440010591 8895879860359535160015887)
          ·
            refine ⟨13343819790539302740023831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8895879860359535160015887 13343819790539302740023831)
            ·
              refine ⟨20015729685808954110035747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13343819790539302740023831 20015729685808954110035747)
              ·
                refine ⟨30023594528713431165053621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20015729685808954110035747 30023594528713431165053621)
                ·
                  refine ⟨2814711987066884171723777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30023594528713431165053621 2814711987066884171723777)
                  ·
                    refine ⟨2111033990300163128792833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2814711987066884171723777 2111033990300163128792833)
                    ·
                      refine ⟨1583275492725122346594625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2111033990300163128792833 1583275492725122346594625)
                      ·
                        rfl

theorem cell23_3083418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_3083418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083418 prefixEnd_3083418 := by exact prefixLift 3083418
  have htrace : WordTrace (prefixWord ++ tailWord_3083418) baseStart_3083418 baseEnd_3083418 := by
    simpa [prefixWord, tailWord_3083418, baseEnd_3083418] using wordTrace_append hprefix tailTrace_3083418
  have hstable : (prefixWord ++ tailWord_3083418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083418).length < 2 ^ (prefixWord ++ tailWord_3083418).sum := by decide
  have hdescent : baseEnd_3083418 < baseStart_3083418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083421 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_3083421 : Nat := 118140960795 + 3083421 * 2 ^ 59
def prefixEnd_3083421 : Nat := 4983230072969 + 3 ^ 40 * 3083421 * 2
def baseEnd_3083421 : Nat := 1583277033167085834857111

theorem tailTrace_3083421 : CollatzResearch.WordTrace tailWord_3083421 prefixEnd_3083421 1583277033167085834857111 := by
  unfold tailWord_3083421
  simp only [CollatzResearch.WordTrace]
  refine ⟨112461602962299798226634117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74974401974866532151089411 112461602962299798226634117)
  ·
    refine ⟨21086550555431212167493897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112461602962299798226634117 21086550555431212167493897)
    ·
      refine ⟨15814912916573409125620423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21086550555431212167493897 15814912916573409125620423)
      ·
        refine ⟨23722369374860113688430635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15814912916573409125620423 23722369374860113688430635)
        ·
          refine ⟨35583554062290170532645953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23722369374860113688430635 35583554062290170532645953)
          ·
            refine ⟨26687665546717627899484465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35583554062290170532645953 26687665546717627899484465)
            ·
              refine ⟨20015749160038220924613349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26687665546717627899484465 20015749160038220924613349)
              ·
                refine ⟨3752952967507166423365003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20015749160038220924613349 3752952967507166423365003)
                ·
                  refine ⟨5629429451260749635047505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752952967507166423365003 5629429451260749635047505)
                  ·
                    refine ⟨4222072088445562226285629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5629429451260749635047505 4222072088445562226285629)
                    ·
                      refine ⟨1583277033167085834857111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4222072088445562226285629 1583277033167085834857111)
                      ·
                        rfl

theorem cell23_3083421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_3083421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083421 prefixEnd_3083421 := by exact prefixLift 3083421
  have htrace : WordTrace (prefixWord ++ tailWord_3083421) baseStart_3083421 baseEnd_3083421 := by
    simpa [prefixWord, tailWord_3083421, baseEnd_3083421] using wordTrace_append hprefix tailTrace_3083421
  have hstable : (prefixWord ++ tailWord_3083421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083421).length < 2 ^ (prefixWord ++ tailWord_3083421).sum := by decide
  have hdescent : baseEnd_3083421 < baseStart_3083421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083424 : List Nat := [2, 1, 1, 4, 2, 1, 5, 7]
def baseStart_3083424 : Nat := 118140960795 + 3083424 * 2 ^ 59
def prefixEnd_3083424 : Nat := 4983230072969 + 3 ^ 40 * 3083424 * 2
def baseEnd_3083424 : Nat := 58639947170705530485911

theorem tailTrace_3083424 : CollatzResearch.WordTrace tailWord_3083424 prefixEnd_3083424 58639947170705530485911 := by
  unfold tailWord_3083424
  simp only [CollatzResearch.WordTrace]
  refine ⟨56230856190644464869496663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74974474920859286492662217 56230856190644464869496663)
  ·
    refine ⟨84346284285966697304244995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56230856190644464869496663 84346284285966697304244995)
    ·
      refine ⟨126519426428950045956367493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84346284285966697304244995 126519426428950045956367493)
      ·
        refine ⟨23722392455428133616818905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126519426428950045956367493 23722392455428133616818905)
        ·
          refine ⟨17791794341571100212614179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23722392455428133616818905 17791794341571100212614179)
          ·
            refine ⟨26687691512356650318921269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17791794341571100212614179 26687691512356650318921269)
            ·
              refine ⟨2501971079283435967398869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26687691512356650318921269 2501971079283435967398869)
              ·
                refine ⟨58639947170705530485911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2501971079283435967398869 58639947170705530485911)
                ·
                  rfl

theorem cell23_3083424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 7].length) (baseStart_3083424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083424 prefixEnd_3083424 := by exact prefixLift 3083424
  have htrace : WordTrace (prefixWord ++ tailWord_3083424) baseStart_3083424 baseEnd_3083424 := by
    simpa [prefixWord, tailWord_3083424, baseEnd_3083424] using wordTrace_append hprefix tailTrace_3083424
  have hstable : (prefixWord ++ tailWord_3083424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083424).length < 2 ^ (prefixWord ++ tailWord_3083424).sum := by decide
  have hdescent : baseEnd_3083424 < baseStart_3083424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083431 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3083431 : Nat := 118140960795 + 3083431 * 2 ^ 59
def prefixEnd_3083431 : Nat := 4983230072969 + 3 ^ 40 * 3083431 * 2
def baseEnd_3083431 : Nat := 1583282167973630795732065

theorem tailTrace_3083431 : CollatzResearch.WordTrace tailWord_3083431 prefixEnd_3083431 1583282167973630795732065 := by
  unfold tailWord_3083431
  simp only [CollatzResearch.WordTrace]
  refine ⟨112461967692263569934498147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74974645128175713289665431 112461967692263569934498147)
  ·
    refine ⟨168692951538395354901747221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112461967692263569934498147 168692951538395354901747221)
    ·
      refine ⟨7907482103362282261019401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168692951538395354901747221 7907482103362282261019401)
      ·
        refine ⟨5930611577521711695764551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7907482103362282261019401 5930611577521711695764551)
        ·
          refine ⟨8895917366282567543646827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5930611577521711695764551 8895917366282567543646827)
          ·
            refine ⟨13343876049423851315470241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8895917366282567543646827 13343876049423851315470241)
            ·
              refine ⟨10007907037067888486602681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13343876049423851315470241 10007907037067888486602681)
              ·
                refine ⟨7505930277800916364952011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10007907037067888486602681 7505930277800916364952011)
                ·
                  refine ⟨11258895416701374547428017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7505930277800916364952011 11258895416701374547428017)
                  ·
                    refine ⟨8444171562526030910571013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11258895416701374547428017 8444171562526030910571013)
                    ·
                      refine ⟨1583282167973630795732065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8444171562526030910571013 1583282167973630795732065)
                      ·
                        rfl

theorem cell23_3083431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3083431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083431 prefixEnd_3083431 := by exact prefixLift 3083431
  have htrace : WordTrace (prefixWord ++ tailWord_3083431) baseStart_3083431 baseEnd_3083431 := by
    simpa [prefixWord, tailWord_3083431, baseEnd_3083431] using wordTrace_append hprefix tailTrace_3083431
  have hstable : (prefixWord ++ tailWord_3083431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083431).length < 2 ^ (prefixWord ++ tailWord_3083431).sum := by decide
  have hdescent : baseEnd_3083431 < baseStart_3083431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083451 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 3]
def baseStart_3083451 : Nat := 118140960795 + 3083451 * 2 ^ 59
def prefixEnd_3083451 : Nat := 4983230072969 + 3 ^ 40 * 3083451 * 2
def baseEnd_3083451 : Nat := 1583292437586720717481973

theorem tailTrace_3083451 : CollatzResearch.WordTrace tailWord_3083451 prefixEnd_3083451 1583292437586720717481973 := by
  unfold tailWord_3083451
  simp only [CollatzResearch.WordTrace]
  refine ⟨112462697152191113350226207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74975131434794075566817471 112462697152191113350226207)
  ·
    refine ⟨168694045728286670025339311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112462697152191113350226207 168694045728286670025339311)
    ·
      refine ⟨253041068592430005038008967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168694045728286670025339311 253041068592430005038008967)
      ·
        refine ⟨379561602888645007557013451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253041068592430005038008967 379561602888645007557013451)
        ·
          refine ⟨569342404332967511335520177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379561602888645007557013451 569342404332967511335520177)
          ·
            refine ⟨427006803249725633501640133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569342404332967511335520177 427006803249725633501640133)
            ·
              refine ⟨80063775609323556281557525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 427006803249725633501640133 80063775609323556281557525)
              ·
                refine ⟨3752989481687041700698009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80063775609323556281557525 3752989481687041700698009)
                ·
                  refine ⟨2814742111265281275523507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3752989481687041700698009 2814742111265281275523507)
                  ·
                    refine ⟨4222113166897921913285261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2814742111265281275523507 4222113166897921913285261)
                    ·
                      refine ⟨1583292437586720717481973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4222113166897921913285261 1583292437586720717481973)
                      ·
                        rfl

theorem cell23_3083451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 3].length) (baseStart_3083451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083451 prefixEnd_3083451 := by exact prefixLift 3083451
  have htrace : WordTrace (prefixWord ++ tailWord_3083451) baseStart_3083451 baseEnd_3083451 := by
    simpa [prefixWord, tailWord_3083451, baseEnd_3083451] using wordTrace_append hprefix tailTrace_3083451
  have hstable : (prefixWord ++ tailWord_3083451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083451).length < 2 ^ (prefixWord ++ tailWord_3083451).sum := by decide
  have hdescent : baseEnd_3083451 < baseStart_3083451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083462 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3083462 : Nat := 118140960795 + 3083462 * 2 ^ 59
def prefixEnd_3083462 : Nat := 4983230072969 + 3 ^ 40 * 3083462 * 2
def baseEnd_3083462 : Nat := 527766028624640058148141

theorem tailTrace_3083462 : CollatzResearch.WordTrace tailWord_3083462 prefixEnd_3083462 527766028624640058148141 := by
  unfold tailWord_3083462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514471823598476944652395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74975398903434174819251093 3514471823598476944652395)
  ·
    refine ⟨5271707735397715416978593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3514471823598476944652395 5271707735397715416978593)
    ·
      refine ⟨3953780801548286562733945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5271707735397715416978593 3953780801548286562733945)
      ·
        refine ⟨2965335601161214922050459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3953780801548286562733945 2965335601161214922050459)
        ·
          refine ⟨4448003401741822383075689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965335601161214922050459 4448003401741822383075689)
          ·
            refine ⟨3336002551306366787306767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4448003401741822383075689 3336002551306366787306767)
            ·
              refine ⟨5004003826959550180960151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336002551306366787306767 5004003826959550180960151)
              ·
                refine ⟨7506005740439325271440227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004003826959550180960151 7506005740439325271440227)
                ·
                  refine ⟨11259008610658987907160341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7506005740439325271440227 11259008610658987907160341)
                  ·
                    refine ⟨527766028624640058148141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11259008610658987907160341 527766028624640058148141)
                    ·
                      rfl

theorem cell23_3083462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3083462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083462 prefixEnd_3083462 := by exact prefixLift 3083462
  have htrace : WordTrace (prefixWord ++ tailWord_3083462) baseStart_3083462 baseEnd_3083462 := by
    simpa [prefixWord, tailWord_3083462, baseEnd_3083462] using wordTrace_append hprefix tailTrace_3083462
  have hstable : (prefixWord ++ tailWord_3083462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083462).length < 2 ^ (prefixWord ++ tailWord_3083462).sum := by decide
  have hdescent : baseEnd_3083462 < baseStart_3083462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083467 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 1, 8]
def baseStart_3083467 : Nat := 118140960795 + 3083467 * 2 ^ 59
def prefixEnd_3083467 : Nat := 4983230072969 + 3 ^ 40 * 3083467 * 2
def baseEnd_3083467 : Nat := 527766884425730884960633

theorem tailTrace_3083467 : CollatzResearch.WordTrace tailWord_3083467 prefixEnd_3083467 527766884425730884960633 := by
  unfold tailWord_3083467
  simp only [CollatzResearch.WordTrace]
  refine ⟨112463280720133148082808655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74975520480088765388539103 112463280720133148082808655)
  ·
    refine ⟨168694921080199722124212983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112463280720133148082808655 168694921080199722124212983)
    ·
      refine ⟨253042381620299583186319475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168694921080199722124212983 253042381620299583186319475)
      ·
        refine ⟨379563572430449374779479213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253042381620299583186319475 379563572430449374779479213)
        ·
          refine ⟨142336339661418515542304705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379563572430449374779479213 142336339661418515542304705)
          ·
            refine ⟨106752254746063886656728529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142336339661418515542304705 106752254746063886656728529)
            ·
              refine ⟨80064191059547914992546397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106752254746063886656728529 80064191059547914992546397)
              ·
                refine ⟨30024071647330468122204899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80064191059547914992546397 30024071647330468122204899)
                ·
                  refine ⟨45036107470995702183307349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30024071647330468122204899 45036107470995702183307349)
                  ·
                    refine ⟨527766884425730884960633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45036107470995702183307349 527766884425730884960633)
                    ·
                      rfl

theorem cell23_3083467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 8].length) (baseStart_3083467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083467 prefixEnd_3083467 := by exact prefixLift 3083467
  have htrace : WordTrace (prefixWord ++ tailWord_3083467) baseStart_3083467 baseEnd_3083467 := by
    simpa [prefixWord, tailWord_3083467, baseEnd_3083467] using wordTrace_append hprefix tailTrace_3083467
  have hstable : (prefixWord ++ tailWord_3083467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083467).length < 2 ^ (prefixWord ++ tailWord_3083467).sum := by decide
  have hdescent : baseEnd_3083467 < baseStart_3083467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083564 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_3083564 : Nat := 118140960795 + 3083564 * 2 ^ 59
def prefixEnd_3083564 : Nat := 4983230072969 + 3 ^ 40 * 3083564 * 2
def baseEnd_3083564 : Nat := 1583350460900678775368953

theorem tailTrace_3083564 : CollatzResearch.WordTrace tailWord_3083564 prefixEnd_3083564 1583350460900678775368953 := by
  unfold tailWord_3083564
  simp only [CollatzResearch.WordTrace]
  refine ⟨56233409300390866824544873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74977879067187822432726497 56233409300390866824544873)
  ·
    refine ⟨42175056975293150118408655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56233409300390866824544873 42175056975293150118408655)
    ·
      refine ⟨63262585462939725177612983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42175056975293150118408655 63262585462939725177612983)
      ·
        refine ⟨94893878194409587766419475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63262585462939725177612983 94893878194409587766419475)
        ·
          refine ⟨142340817291614381649629213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94893878194409587766419475 142340817291614381649629213)
          ·
            refine ⟨53377806484355393118610955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142340817291614381649629213 53377806484355393118610955)
            ·
              refine ⟨80066709726533089677916433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53377806484355393118610955 80066709726533089677916433)
              ·
                refine ⟨60050032294899817258437325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80066709726533089677916433 60050032294899817258437325)
                ·
                  refine ⟨22518762110587431471913997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60050032294899817258437325 22518762110587431471913997)
                  ·
                    refine ⟨8444535791470286801967749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22518762110587431471913997 8444535791470286801967749)
                    ·
                      refine ⟨1583350460900678775368953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8444535791470286801967749 1583350460900678775368953)
                      ·
                        rfl

theorem cell23_3083564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_3083564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083564 prefixEnd_3083564 := by exact prefixLift 3083564
  have htrace : WordTrace (prefixWord ++ tailWord_3083564) baseStart_3083564 baseEnd_3083564 := by
    simpa [prefixWord, tailWord_3083564, baseEnd_3083564] using wordTrace_append hprefix tailTrace_3083564
  have hstable : (prefixWord ++ tailWord_3083564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083564).length < 2 ^ (prefixWord ++ tailWord_3083564).sum := by decide
  have hdescent : baseEnd_3083564 < baseStart_3083564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083565 : List Nat := [1, 5, 3, 1, 1, 2, 1, 4, 5]
def baseStart_3083565 : Nat := 118140960795 + 3083565 * 2 ^ 59
def prefixEnd_3083565 : Nat := 4983230072969 + 3 ^ 40 * 3083565 * 2
def baseEnd_3083565 : Nat := 175927886042370363495161

theorem tailTrace_3083565 : CollatzResearch.WordTrace tailWord_3083565 prefixEnd_3083565 175927886042370363495161 := by
  unfold tailWord_3083565
  simp only [CollatzResearch.WordTrace]
  refine ⟨112466855073778110819876149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74977903382518740546584099 112466855073778110819876149)
  ·
    refine ⟨10543767663166697889363389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112466855073778110819876149 10543767663166697889363389)
    ·
      refine ⟨3953912873687511708511271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10543767663166697889363389 3953912873687511708511271)
      ·
        refine ⟨5930869310531267562766907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3953912873687511708511271 5930869310531267562766907)
        ·
          refine ⟨8896303965796901344150361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5930869310531267562766907 8896303965796901344150361)
          ·
            refine ⟨6672227974347676008112771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8896303965796901344150361 6672227974347676008112771)
            ·
              refine ⟨10008341961521514012169157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672227974347676008112771 10008341961521514012169157)
              ·
                refine ⟨1876564117785283877281717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10008341961521514012169157 1876564117785283877281717)
                ·
                  refine ⟨175927886042370363495161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1876564117785283877281717 175927886042370363495161)
                  ·
                    rfl

theorem cell23_3083565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_3083565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083565 prefixEnd_3083565 := by exact prefixLift 3083565
  have htrace : WordTrace (prefixWord ++ tailWord_3083565) baseStart_3083565 baseEnd_3083565 := by
    simpa [prefixWord, tailWord_3083565, baseEnd_3083565] using wordTrace_append hprefix tailTrace_3083565
  have hstable : (prefixWord ++ tailWord_3083565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083565).length < 2 ^ (prefixWord ++ tailWord_3083565).sum := by decide
  have hdescent : baseEnd_3083565 < baseStart_3083565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083591 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 5, 4]
def baseStart_3083591 : Nat := 118140960795 + 3083591 * 2 ^ 59
def prefixEnd_3083591 : Nat := 4983230072969 + 3 ^ 40 * 3083591 * 2
def baseEnd_3083591 : Nat := 527788108292783389910443

theorem tailTrace_3083591 : CollatzResearch.WordTrace tailWord_3083591 prefixEnd_3083591 527788108292783389910443 := by
  unfold tailWord_3083591
  simp only [CollatzResearch.WordTrace]
  refine ⟨112467803371683917260322627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74978535581122611506881751 112467803371683917260322627)
  ·
    refine ⟨168701705057525875890483941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112467803371683917260322627 168701705057525875890483941)
    ·
      refine ⟨31631569698286101729465739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168701705057525875890483941 31631569698286101729465739)
      ·
        refine ⟨47447354547429152594198609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31631569698286101729465739 47447354547429152594198609)
        ·
          refine ⟨35585515910571864445648957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47447354547429152594198609 35585515910571864445648957)
          ·
            refine ⟨13344568466464449167118359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35585515910571864445648957 13344568466464449167118359)
            ·
              refine ⟨20016852699696673750677539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13344568466464449167118359 20016852699696673750677539)
              ·
                refine ⟨30025279049545010626016309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20016852699696673750677539 30025279049545010626016309)
                ·
                  refine ⟨2814869910894844746189029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30025279049545010626016309 2814869910894844746189029)
                  ·
                    refine ⟨527788108292783389910443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2814869910894844746189029 527788108292783389910443)
                    ·
                      rfl

theorem cell23_3083591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_3083591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083591 prefixEnd_3083591 := by exact prefixLift 3083591
  have htrace : WordTrace (prefixWord ++ tailWord_3083591) baseStart_3083591 baseEnd_3083591 := by
    simpa [prefixWord, tailWord_3083591, baseEnd_3083591] using wordTrace_append hprefix tailTrace_3083591
  have hstable : (prefixWord ++ tailWord_3083591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083591).length < 2 ^ (prefixWord ++ tailWord_3083591).sum := by decide
  have hdescent : baseEnd_3083591 < baseStart_3083591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083594 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3083594 : Nat := 118140960795 + 3083594 * 2 ^ 59
def prefixEnd_3083594 : Nat := 4983230072969 + 3 ^ 40 * 3083594 * 2
def baseEnd_3083594 : Nat := 1583365865320313657993815

theorem tailTrace_3083594 : CollatzResearch.WordTrace tailWord_3083594 prefixEnd_3083594 1583365865320313657993815 := by
  unfold tailWord_3083594
  simp only [CollatzResearch.WordTrace]
  refine ⟨28116978197668262193170459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74978608527115365848454557 28116978197668262193170459)
  ·
    refine ⟨42175467296502393289755689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28116978197668262193170459 42175467296502393289755689)
    ·
      refine ⟨31631600472376794967316767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42175467296502393289755689 31631600472376794967316767)
      ·
        refine ⟨47447400708565192450975151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31631600472376794967316767 47447400708565192450975151)
        ·
          refine ⟨71171101062847788676462727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47447400708565192450975151 71171101062847788676462727)
          ·
            refine ⟨106756651594271683014694091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71171101062847788676462727 106756651594271683014694091)
            ·
              refine ⟨160134977391407524522041137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106756651594271683014694091 160134977391407524522041137)
              ·
                refine ⟨120101233043555643391530853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160134977391407524522041137 120101233043555643391530853)
                ·
                  refine ⟨22518981195666683135912035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120101233043555643391530853 22518981195666683135912035)
                  ·
                    refine ⟨33778471793500024703868053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22518981195666683135912035 33778471793500024703868053)
                    ·
                      refine ⟨1583365865320313657993815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33778471793500024703868053 1583365865320313657993815)
                      ·
                        rfl

theorem cell23_3083594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3083594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083594 prefixEnd_3083594 := by exact prefixLift 3083594
  have htrace : WordTrace (prefixWord ++ tailWord_3083594) baseStart_3083594 baseEnd_3083594 := by
    simpa [prefixWord, tailWord_3083594, baseEnd_3083594] using wordTrace_append hprefix tailTrace_3083594
  have hstable : (prefixWord ++ tailWord_3083594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083594).length < 2 ^ (prefixWord ++ tailWord_3083594).sum := by decide
  have hdescent : baseEnd_3083594 < baseStart_3083594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083601 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_3083601 : Nat := 118140960795 + 3083601 * 2 ^ 59
def prefixEnd_3083601 : Nat := 4983230072969 + 3 ^ 40 * 3083601 * 2
def baseEnd_3083601 : Nat := 1583369459684895130606283

theorem tailTrace_3083601 : CollatzResearch.WordTrace tailWord_3083601 prefixEnd_3083601 1583369459684895130606283 := by
  unfold tailWord_3083601
  simp only [CollatzResearch.WordTrace]
  refine ⟨112468168101647688968186657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74978778734431792645457771 112468168101647688968186657)
  ·
    refine ⟨84351126076235766726139993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112468168101647688968186657 84351126076235766726139993)
    ·
      refine ⟨63263344557176825044604995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84351126076235766726139993 63263344557176825044604995)
      ·
        refine ⟨94895016835765237566907493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63263344557176825044604995 94895016835765237566907493)
        ·
          refine ⟨17792815656705982043795155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94895016835765237566907493 17792815656705982043795155)
          ·
            refine ⟨26689223485058973065692733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17792815656705982043795155 26689223485058973065692733)
            ·
              refine ⟨10008458806897114899634775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26689223485058973065692733 10008458806897114899634775)
              ·
                refine ⟨15012688210345672349452163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10008458806897114899634775 15012688210345672349452163)
                ·
                  refine ⟨22519032315518508524178245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15012688210345672349452163 22519032315518508524178245)
                  ·
                    refine ⟨4222318559159720348283421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22519032315518508524178245 4222318559159720348283421)
                    ·
                      refine ⟨1583369459684895130606283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4222318559159720348283421 1583369459684895130606283)
                      ·
                        rfl

theorem cell23_3083601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_3083601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083601 prefixEnd_3083601 := by exact prefixLift 3083601
  have htrace : WordTrace (prefixWord ++ tailWord_3083601) baseStart_3083601 baseEnd_3083601 := by
    simpa [prefixWord, tailWord_3083601, baseEnd_3083601] using wordTrace_append hprefix tailTrace_3083601
  have hstable : (prefixWord ++ tailWord_3083601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083601).length < 2 ^ (prefixWord ++ tailWord_3083601).sum := by decide
  have hdescent : baseEnd_3083601 < baseStart_3083601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083618 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3083618 : Nat := 118140960795 + 3083618 * 2 ^ 59
def prefixEnd_3083618 : Nat := 4983230072969 + 3 ^ 40 * 3083618 * 2
def baseEnd_3083618 : Nat := 1583378188856021564093705

theorem tailTrace_3083618 : CollatzResearch.WordTrace tailWord_3083618 prefixEnd_3083618 1583378188856021564093705 := by
  unfold tailWord_3083618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28117197035646525217888877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74979192095057400581037005 28117197035646525217888877)
  ·
    refine ⟨10543948888367446956708329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28117197035646525217888877 10543948888367446956708329)
    ·
      refine ⟨7907961666275585217531247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10543948888367446956708329 7907961666275585217531247)
      ·
        refine ⟨11861942499413377826296871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7907961666275585217531247 11861942499413377826296871)
        ·
          refine ⟨17792913749120066739445307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11861942499413377826296871 17792913749120066739445307)
          ·
            refine ⟨26689370623680100109167961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17792913749120066739445307 26689370623680100109167961)
            ·
              refine ⟨20017027967760075081875971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26689370623680100109167961 20017027967760075081875971)
              ·
                refine ⟨30025541951640112622813957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20017027967760075081875971 30025541951640112622813957)
                ·
                  refine ⟨5629789115932521116777617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30025541951640112622813957 5629789115932521116777617)
                  ·
                    refine ⟨4222341836949390837583213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5629789115932521116777617 4222341836949390837583213)
                    ·
                      refine ⟨1583378188856021564093705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4222341836949390837583213 1583378188856021564093705)
                      ·
                        rfl

theorem cell23_3083618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3083618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083618 prefixEnd_3083618 := by exact prefixLift 3083618
  have htrace : WordTrace (prefixWord ++ tailWord_3083618) baseStart_3083618 baseEnd_3083618 := by
    simpa [prefixWord, tailWord_3083618, baseEnd_3083618] using wordTrace_append hprefix tailTrace_3083618
  have hstable : (prefixWord ++ tailWord_3083618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083618).length < 2 ^ (prefixWord ++ tailWord_3083618).sum := by decide
  have hdescent : baseEnd_3083618 < baseStart_3083618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083671 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_3083671 : Nat := 118140960795 + 3083671 * 2 ^ 59
def prefixEnd_3083671 : Nat := 4983230072969 + 3 ^ 40 * 3083671 * 2
def baseEnd_3083671 : Nat := 1583405403330709856730961

theorem tailTrace_3083671 : CollatzResearch.WordTrace tailWord_3083671 prefixEnd_3083671 1583405403330709856730961 := by
  unfold tailWord_3083671
  simp only [CollatzResearch.WordTrace]
  refine ⟨112470721211394090923234867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74980480807596060615489911 112470721211394090923234867)
  ·
    refine ⟨168706081817091136384852301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112470721211394090923234867 168706081817091136384852301)
    ·
      refine ⟨63264780681409176144319613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168706081817091136384852301 63264780681409176144319613)
      ·
        refine ⟨23724292755528441054119855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63264780681409176144319613 23724292755528441054119855)
        ·
          refine ⟨35586439133292661581179783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23724292755528441054119855 35586439133292661581179783)
          ·
            refine ⟨53379658699938992371769675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35586439133292661581179783 53379658699938992371769675)
            ·
              refine ⟨80069488049908488557654513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53379658699938992371769675 80069488049908488557654513)
              ·
                refine ⟨60052116037431366418240885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80069488049908488557654513 60052116037431366418240885)
                ·
                  refine ⟨5629885878509190601710083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60052116037431366418240885 5629885878509190601710083)
                  ·
                    refine ⟨8444828817763785902565125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5629885878509190601710083 8444828817763785902565125)
                    ·
                      refine ⟨1583405403330709856730961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8444828817763785902565125 1583405403330709856730961)
                      ·
                        rfl

theorem cell23_3083671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_3083671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083671 prefixEnd_3083671 := by exact prefixLift 3083671
  have htrace : WordTrace (prefixWord ++ tailWord_3083671) baseStart_3083671 baseEnd_3083671 := by
    simpa [prefixWord, tailWord_3083671, baseEnd_3083671] using wordTrace_append hprefix tailTrace_3083671
  have hstable : (prefixWord ++ tailWord_3083671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083671).length < 2 ^ (prefixWord ++ tailWord_3083671).sum := by decide
  have hdescent : baseEnd_3083671 < baseStart_3083671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083682 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3083682 : Nat := 118140960795 + 3083682 * 2 ^ 59
def prefixEnd_3083682 : Nat := 4983230072969 + 3 ^ 40 * 3083682 * 2
def baseEnd_3083682 : Nat := 1583411051617909313693411

theorem tailTrace_3083682 : CollatzResearch.WordTrace tailWord_3083682 prefixEnd_3083682 1583411051617909313693411 := by
  unfold tailWord_3083682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28117780603588559950471325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74980748276236159867923533 28117780603588559950471325)
  ·
    refine ⟨10544167726345709981426747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28117780603588559950471325 10544167726345709981426747)
    ·
      refine ⟨15816251589518564972140121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10544167726345709981426747 15816251589518564972140121)
      ·
        refine ⟨11862188692138923729105091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15816251589518564972140121 11862188692138923729105091)
        ·
          refine ⟨17793283038208385593657637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11862188692138923729105091 17793283038208385593657637)
          ·
            refine ⟨3336240569664072298810807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17793283038208385593657637 3336240569664072298810807)
            ·
              refine ⟨5004360854496108448216211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336240569664072298810807 5004360854496108448216211)
              ·
                refine ⟨7506541281744162672324317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004360854496108448216211 7506541281744162672324317)
                ·
                  refine ⟨2814952980654061002121619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7506541281744162672324317 2814952980654061002121619)
                  ·
                    refine ⟨4222429470981091503182429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2814952980654061002121619 4222429470981091503182429)
                    ·
                      refine ⟨1583411051617909313693411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4222429470981091503182429 1583411051617909313693411)
                      ·
                        rfl

theorem cell23_3083682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3083682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083682 prefixEnd_3083682 := by exact prefixLift 3083682
  have htrace : WordTrace (prefixWord ++ tailWord_3083682) baseStart_3083682 baseEnd_3083682 := by
    simpa [prefixWord, tailWord_3083682, baseEnd_3083682] using wordTrace_append hprefix tailTrace_3083682
  have hstable : (prefixWord ++ tailWord_3083682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083682).length < 2 ^ (prefixWord ++ tailWord_3083682).sum := by decide
  have hdescent : baseEnd_3083682 < baseStart_3083682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083732 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_3083732 : Nat := 118140960795 + 3083732 * 2 ^ 59
def prefixEnd_3083732 : Nat := 4983230072969 + 3 ^ 40 * 3083732 * 2
def baseEnd_3083732 : Nat := 527812241883544706022727

theorem tailTrace_3083732 : CollatzResearch.WordTrace tailWord_3083732 prefixEnd_3083732 527812241883544706022727 := by
  unfold tailWord_3083732
  simp only [CollatzResearch.WordTrace]
  refine ⟨56236473032086549170602725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74981964042782065560803633 56236473032086549170602725)
  ·
    refine ⟨10544338693516227969488011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56236473032086549170602725 10544338693516227969488011)
    ·
      refine ⟨15816508040274341954232017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10544338693516227969488011 15816508040274341954232017)
      ·
        refine ⟨11862381030205756465674013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15816508040274341954232017 11862381030205756465674013)
        ·
          refine ⟨4448392886327158674627755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11862381030205756465674013 4448392886327158674627755)
          ·
            refine ⟨6672589329490738011941633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448392886327158674627755 6672589329490738011941633)
            ·
              refine ⟨5004441997118053508956225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6672589329490738011941633 5004441997118053508956225)
              ·
                refine ⟨3753331497838540131717169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5004441997118053508956225 3753331497838540131717169)
                ·
                  refine ⟨2814998623378905098787877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3753331497838540131717169 2814998623378905098787877)
                  ·
                    refine ⟨527812241883544706022727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2814998623378905098787877 527812241883544706022727)
                    ·
                      rfl

theorem cell23_3083732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_3083732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083732 prefixEnd_3083732 := by exact prefixLift 3083732
  have htrace : WordTrace (prefixWord ++ tailWord_3083732) baseStart_3083732 baseEnd_3083732 := by
    simpa [prefixWord, tailWord_3083732, baseEnd_3083732] using wordTrace_append hprefix tailTrace_3083732
  have hstable : (prefixWord ++ tailWord_3083732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083732).length < 2 ^ (prefixWord ++ tailWord_3083732).sum := by decide
  have hdescent : baseEnd_3083732 < baseStart_3083732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083781 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_3083781 : Nat := 118140960795 + 3083781 * 2 ^ 59
def prefixEnd_3083781 : Nat := 4983230072969 + 3 ^ 40 * 3083781 * 2
def baseEnd_3083781 : Nat := 1583461886202704426355455

theorem tailTrace_3083781 : CollatzResearch.WordTrace tailWord_3083781 prefixEnd_3083781 1583461886202704426355455 := by
  unfold tailWord_3083781
  simp only [CollatzResearch.WordTrace]
  refine ⟨112474733240995579709739197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74983155493997053139826131 112474733240995579709739197)
  ·
    refine ⟨42178024965373342391152199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112474733240995579709739197 42178024965373342391152199)
    ·
      refine ⟨63267037448060013586728299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42178024965373342391152199 63267037448060013586728299)
      ·
        refine ⟨94900556172090020380092449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63267037448060013586728299 94900556172090020380092449)
        ·
          refine ⟨71175417129067515285069337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94900556172090020380092449 71175417129067515285069337)
          ·
            refine ⟨53381562846800636463802003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71175417129067515285069337 53381562846800636463802003)
            ·
              refine ⟨80072344270200954695703005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53381562846800636463802003 80072344270200954695703005)
              ·
                refine ⟨30027129101325358010888627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80072344270200954695703005 30027129101325358010888627)
                ·
                  refine ⟨45040693651988037016332941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30027129101325358010888627 45040693651988037016332941)
                  ·
                    refine ⟨16890260119495513881124853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45040693651988037016332941 16890260119495513881124853)
                    ·
                      refine ⟨1583461886202704426355455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16890260119495513881124853 1583461886202704426355455)
                      ·
                        rfl

theorem cell23_3083781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_3083781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083781 prefixEnd_3083781 := by exact prefixLift 3083781
  have htrace : WordTrace (prefixWord ++ tailWord_3083781) baseStart_3083781 baseEnd_3083781 := by
    simpa [prefixWord, tailWord_3083781, baseEnd_3083781] using wordTrace_append hprefix tailTrace_3083781
  have hstable : (prefixWord ++ tailWord_3083781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083781).length < 2 ^ (prefixWord ++ tailWord_3083781).sum := by decide
  have hdescent : baseEnd_3083781 < baseStart_3083781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083818 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 7]
def baseStart_3083818 : Nat := 118140960795 + 3083818 * 2 ^ 59
def prefixEnd_3083818 : Nat := 4983230072969 + 3 ^ 40 * 3083818 * 2
def baseEnd_3083818 : Nat := 175942320554102309065865

theorem tailTrace_3083818 : CollatzResearch.WordTrace tailWord_3083818 prefixEnd_3083818 175942320554102309065865 := by
  unfold tailWord_3083818
  simp only [CollatzResearch.WordTrace]
  refine ⟨28119020685465383757209027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74984055161241023352557405 28119020685465383757209027)
  ·
    refine ⟨42178531028198075635813541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28119020685465383757209027 42178531028198075635813541)
    ·
      refine ⟨7908474567787139181715039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42178531028198075635813541 7908474567787139181715039)
      ·
        refine ⟨11862711851680708772572559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7908474567787139181715039 11862711851680708772572559)
        ·
          refine ⟨17794067777521063158858839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11862711851680708772572559 17794067777521063158858839)
          ·
            refine ⟨26691101666281594738288259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17794067777521063158858839 26691101666281594738288259)
            ·
              refine ⟨40036652499422392107432389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26691101666281594738288259 40036652499422392107432389)
              ·
                refine ⟨7506872343641698520143573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40036652499422392107432389 7506872343641698520143573)
                ·
                  refine ⟨175942320554102309065865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7506872343641698520143573 175942320554102309065865)
                  ·
                    rfl

theorem cell23_3083818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_3083818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083818 prefixEnd_3083818 := by exact prefixLift 3083818
  have htrace : WordTrace (prefixWord ++ tailWord_3083818) baseStart_3083818 baseEnd_3083818 := by
    simpa [prefixWord, tailWord_3083818, baseEnd_3083818] using wordTrace_append hprefix tailTrace_3083818
  have hstable : (prefixWord ++ tailWord_3083818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083818).length < 2 ^ (prefixWord ++ tailWord_3083818).sum := by decide
  have hdescent : baseEnd_3083818 < baseStart_3083818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083852 : List Nat := [2, 2, 1, 3, 1, 4, 3, 2, 5]
def baseStart_3083852 : Nat := 118140960795 + 3083852 * 2 ^ 59
def prefixEnd_3083852 : Nat := 4983230072969 + 3 ^ 40 * 3083852 * 2
def baseEnd_3083852 : Nat := 175944260369908183174181

theorem tailTrace_3083852 : CollatzResearch.WordTrace tailWord_3083852 prefixEnd_3083852 175944260369908183174181 := by
  unfold tailWord_3083852
  simp only [CollatzResearch.WordTrace]
  refine ⟨56238661411869179417786905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74984881882492239223715873 56238661411869179417786905)
  ·
    refine ⟨42178996058901884563340179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56238661411869179417786905 42178996058901884563340179)
    ·
      refine ⟨63268494088352826845010269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42178996058901884563340179 63268494088352826845010269)
      ·
        refine ⟨23725685283132310066878851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63268494088352826845010269 23725685283132310066878851)
        ·
          refine ⟨35588527924698465100318277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23725685283132310066878851 35588527924698465100318277)
          ·
            refine ⟨6672848985880962206309677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35588527924698465100318277 6672848985880962206309677)
            ·
              refine ⟨2502318369705360827366129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6672848985880962206309677 2502318369705360827366129)
              ·
                refine ⟨1876738777279020620524597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502318369705360827366129 1876738777279020620524597)
                ·
                  refine ⟨175944260369908183174181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1876738777279020620524597 175944260369908183174181)
                  ·
                    rfl

theorem cell23_3083852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_3083852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083852 prefixEnd_3083852 := by exact prefixLift 3083852
  have htrace : WordTrace (prefixWord ++ tailWord_3083852) baseStart_3083852 baseEnd_3083852 := by
    simpa [prefixWord, tailWord_3083852, baseEnd_3083852] using wordTrace_append hprefix tailTrace_3083852
  have hstable : (prefixWord ++ tailWord_3083852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083852).length < 2 ^ (prefixWord ++ tailWord_3083852).sum := by decide
  have hdescent : baseEnd_3083852 < baseStart_3083852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083858 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3083858 : Nat := 118140960795 + 3083858 * 2 ^ 59
def prefixEnd_3083858 : Nat := 4983230072969 + 3 ^ 40 * 3083858 * 2
def baseEnd_3083858 : Nat := 1583501424213100625092601

theorem tailTrace_3083858 : CollatzResearch.WordTrace tailWord_3083858 prefixEnd_3083858 1583501424213100625092601 := by
  unfold tailWord_3083858
  simp only [CollatzResearch.WordTrace]
  refine ⟨28119385415429155465073057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74985027774477747906861485 28119385415429155465073057)
  ·
    refine ⟨21089539061571866598804793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28119385415429155465073057 21089539061571866598804793)
    ·
      refine ⟨15817154296178899949103595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21089539061571866598804793 15817154296178899949103595)
      ·
        refine ⟨23725731444268349923655393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15817154296178899949103595 23725731444268349923655393)
        ·
          refine ⟨17794298583201262442741545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23725731444268349923655393 17794298583201262442741545)
          ·
            refine ⟨13345723937400946832056159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17794298583201262442741545 13345723937400946832056159)
            ·
              refine ⟨20018585906101420248084239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13345723937400946832056159 20018585906101420248084239)
              ·
                refine ⟨30027878859152130372126359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20018585906101420248084239 30027878859152130372126359)
                ·
                  refine ⟨45041818288728195558189539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30027878859152130372126359 45041818288728195558189539)
                  ·
                    refine ⟨67562727433092293337284309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45041818288728195558189539 67562727433092293337284309)
                    ·
                      refine ⟨1583501424213100625092601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67562727433092293337284309 1583501424213100625092601)
                      ·
                        rfl

theorem cell23_3083858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3083858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083858 prefixEnd_3083858 := by exact prefixLift 3083858
  have htrace : WordTrace (prefixWord ++ tailWord_3083858) baseStart_3083858 baseEnd_3083858 := by
    simpa [prefixWord, tailWord_3083858, baseEnd_3083858] using wordTrace_append hprefix tailTrace_3083858
  have hstable : (prefixWord ++ tailWord_3083858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083858).length < 2 ^ (prefixWord ++ tailWord_3083858).sum := by decide
  have hdescent : baseEnd_3083858 < baseStart_3083858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083955 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 1, 5]
def baseStart_3083955 : Nat := 118140960795 + 3083955 * 2 ^ 59
def prefixEnd_3083955 : Nat := 4983230072969 + 3 ^ 40 * 3083955 * 2
def baseEnd_3083955 : Nat := 527850410612195581859885

theorem tailTrace_3083955 : CollatzResearch.WordTrace tailWord_3083955 prefixEnd_3083955 527850410612195581859885 := by
  unfold tailWord_3083955
  simp only [CollatzResearch.WordTrace]
  refine ⟨112481079542365207426573319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74987386361576804951048879 112481079542365207426573319)
  ·
    refine ⟨168721619313547811139859979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112481079542365207426573319 168721619313547811139859979)
    ·
      refine ⟨253082428970321716709789969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168721619313547811139859979 253082428970321716709789969)
      ·
        refine ⟨189811821727741287532342477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253082428970321716709789969 189811821727741287532342477)
        ·
          refine ⟨71179433147902982824628429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189811821727741287532342477 71179433147902982824628429)
          ·
            refine ⟨26692287430463618559235661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71179433147902982824628429 26692287430463618559235661)
            ·
              refine ⟨10009607786423856959713373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26692287430463618559235661 10009607786423856959713373)
              ·
                refine ⟨3753602919908946359892515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10009607786423856959713373 3753602919908946359892515)
                ·
                  refine ⟨5630404379863419539838773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753602919908946359892515 5630404379863419539838773)
                  ·
                    refine ⟨527850410612195581859885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5630404379863419539838773 527850410612195581859885)
                    ·
                      rfl

theorem cell23_3083955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 5].length) (baseStart_3083955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083955 prefixEnd_3083955 := by exact prefixLift 3083955
  have htrace : WordTrace (prefixWord ++ tailWord_3083955) baseStart_3083955 baseEnd_3083955 := by
    simpa [prefixWord, tailWord_3083955, baseEnd_3083955] using wordTrace_append hprefix tailTrace_3083955
  have hstable : (prefixWord ++ tailWord_3083955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083955).length < 2 ^ (prefixWord ++ tailWord_3083955).sum := by decide
  have hdescent : baseEnd_3083955 < baseStart_3083955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083985 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 1, 6]
def baseStart_3083985 : Nat := 118140960795 + 3083985 * 2 ^ 59
def prefixEnd_3083985 : Nat := 4983230072969 + 3 ^ 40 * 3083985 * 2
def baseEnd_3083985 : Nat := 527855545418740542734839

theorem tailTrace_3083985 : CollatzResearch.WordTrace tailWord_3083985 prefixEnd_3083985 527855545418740542734839 := by
  unfold tailWord_3083985
  simp only [CollatzResearch.WordTrace]
  refine ⟨112482173732256522550165409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74988115821504348366776939 112482173732256522550165409)
  ·
    refine ⟨84361630299192391912624057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112482173732256522550165409 84361630299192391912624057)
    ·
      refine ⟨63271222724394293934468043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84361630299192391912624057 63271222724394293934468043)
      ·
        refine ⟨94906834086591440901702065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63271222724394293934468043 94906834086591440901702065)
        ·
          refine ⟨71180125564943580676276549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94906834086591440901702065 71180125564943580676276549)
          ·
            refine ⟨13346273543426921376801853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71180125564943580676276549 13346273543426921376801853)
            ·
              refine ⟨5004852578785095516300695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13346273543426921376801853 5004852578785095516300695)
              ·
                refine ⟨7507278868177643274451043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004852578785095516300695 7507278868177643274451043)
                ·
                  refine ⟨11260918302266464911676565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7507278868177643274451043 11260918302266464911676565)
                  ·
                    refine ⟨527855545418740542734839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11260918302266464911676565 527855545418740542734839)
                    ·
                      rfl

theorem cell23_3083985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_3083985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083985 prefixEnd_3083985 := by exact prefixLift 3083985
  have htrace : WordTrace (prefixWord ++ tailWord_3083985) baseStart_3083985 baseEnd_3083985 := by
    simpa [prefixWord, tailWord_3083985, baseEnd_3083985] using wordTrace_append hprefix tailTrace_3083985
  have hstable : (prefixWord ++ tailWord_3083985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083985).length < 2 ^ (prefixWord ++ tailWord_3083985).sum := by decide
  have hdescent : baseEnd_3083985 < baseStart_3083985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083992 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 1, 1, 4]
def baseStart_3083992 : Nat := 118140960795 + 3083992 * 2 ^ 59
def prefixEnd_3083992 : Nat := 4983230072969 + 3 ^ 40 * 3083992 * 2
def baseEnd_3083992 : Nat := 1583570230620803100816985

theorem tailTrace_3083992 : CollatzResearch.WordTrace tailWord_3083992 prefixEnd_3083992 1583570230620803100816985 := by
  unfold tailWord_3083992
  simp only [CollatzResearch.WordTrace]
  refine ⟨56241214521615581372835115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74988286028820775163780153 56241214521615581372835115)
  ·
    refine ⟨84361821782423372059252673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56241214521615581372835115 84361821782423372059252673)
    ·
      refine ⟨63271366336817529044439505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84361821782423372059252673 63271366336817529044439505)
      ·
        refine ⟨47453524752613146783329629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63271366336817529044439505 47453524752613146783329629)
        ·
          refine ⟨17795071782229930043748611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47453524752613146783329629 17795071782229930043748611)
          ·
            refine ⟨26692607673344895065622917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17795071782229930043748611 26692607673344895065622917)
            ·
              refine ⟨5004863938752167824804297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26692607673344895065622917 5004863938752167824804297)
              ·
                refine ⟨3753647954064125868603223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5004863938752167824804297 3753647954064125868603223)
                ·
                  refine ⟨5630471931096188802904835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753647954064125868603223 5630471931096188802904835)
                  ·
                    refine ⟨8445707896644283204357253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5630471931096188802904835 8445707896644283204357253)
                    ·
                      refine ⟨1583570230620803100816985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8445707896644283204357253 1583570230620803100816985)
                      ·
                        rfl

theorem cell23_3083992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_3083992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3083992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3083992 prefixEnd_3083992 := by exact prefixLift 3083992
  have htrace : WordTrace (prefixWord ++ tailWord_3083992) baseStart_3083992 baseEnd_3083992 := by
    simpa [prefixWord, tailWord_3083992, baseEnd_3083992] using wordTrace_append hprefix tailTrace_3083992
  have hstable : (prefixWord ++ tailWord_3083992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083992).length < 2 ^ (prefixWord ++ tailWord_3083992).sum := by decide
  have hdescent : baseEnd_3083992 < baseStart_3083992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084003 : List Nat := [1, 1, 1, 7, 2, 2, 1, 3, 1, 1, 3]
def baseStart_3084003 : Nat := 118140960795 + 3084003 * 2 ^ 59
def prefixEnd_3084003 : Nat := 4983230072969 + 3 ^ 40 * 3084003 * 2
def baseEnd_3084003 : Nat := 1583575878908002557779435

theorem tailTrace_3084003 : CollatzResearch.WordTrace tailWord_3084003 prefixEnd_3084003 1583575878908002557779435 := by
  unfold tailWord_3084003
  simp only [CollatzResearch.WordTrace]
  refine ⟨112482830246191311624320663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74988553497460874416213775 112482830246191311624320663)
  ·
    refine ⟨168724245369286967436480995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112482830246191311624320663 168724245369286967436480995)
    ·
      refine ⟨253086368053930451154721493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168724245369286967436480995 253086368053930451154721493)
      ·
        refine ⟨5931711751263994948938785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 253086368053930451154721493 5931711751263994948938785)
        ·
          refine ⟨4448783813447996211704089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5931711751263994948938785 4448783813447996211704089)
          ·
            refine ⟨3336587860085997158778067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4448783813447996211704089 3336587860085997158778067)
            ·
              refine ⟨5004881790128995738167101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336587860085997158778067 5004881790128995738167101)
              ·
                refine ⟨1876830671298373401812663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5004881790128995738167101 1876830671298373401812663)
                ·
                  refine ⟨2815246006947560102718995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876830671298373401812663 2815246006947560102718995)
                  ·
                    refine ⟨4222869010421340154078493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2815246006947560102718995 4222869010421340154078493)
                    ·
                      refine ⟨1583575878908002557779435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4222869010421340154078493 1583575878908002557779435)
                      ·
                        rfl

theorem cell23_3084003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_3084003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084003 prefixEnd_3084003 := by exact prefixLift 3084003
  have htrace : WordTrace (prefixWord ++ tailWord_3084003) baseStart_3084003 baseEnd_3084003 := by
    simpa [prefixWord, tailWord_3084003, baseEnd_3084003] using wordTrace_append hprefix tailTrace_3084003
  have hstable : (prefixWord ++ tailWord_3084003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084003).length < 2 ^ (prefixWord ++ tailWord_3084003).sum := by decide
  have hdescent : baseEnd_3084003 < baseStart_3084003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084005 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3084005 : Nat := 118140960795 + 3084005 * 2 ^ 59
def prefixEnd_3084005 : Nat := 4983230072969 + 3 ^ 40 * 3084005 * 2
def baseEnd_3084005 : Nat := 1583576905869311549954425

theorem tailTrace_3084005 : CollatzResearch.WordTrace tailWord_3084005 prefixEnd_3084005 1583576905869311549954425 := by
  unfold tailWord_3084005
  simp only [CollatzResearch.WordTrace]
  refine ⟨112482903192184065965893469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74988602128122710643928979 112482903192184065965893469)
  ·
    refine ⟨42181088697069024737210051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112482903192184065965893469 42181088697069024737210051)
    ·
      refine ⟨63271633045603537105815077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42181088697069024737210051 63271633045603537105815077)
      ·
        refine ⟨11863431196050663207340327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63271633045603537105815077 11863431196050663207340327)
        ·
          refine ⟨17795146794075994811010491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11863431196050663207340327 17795146794075994811010491)
          ·
            refine ⟨26692720191113992216515737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17795146794075994811010491 26692720191113992216515737)
            ·
              refine ⟨20019540143335494162386803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26692720191113992216515737 20019540143335494162386803)
              ·
                refine ⟨30029310215003241243580205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20019540143335494162386803 30029310215003241243580205)
                ·
                  refine ⟨11260991330626215466342577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30029310215003241243580205 11260991330626215466342577)
                  ·
                    refine ⟨8445743497969661599756933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11260991330626215466342577 8445743497969661599756933)
                    ·
                      refine ⟨1583576905869311549954425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8445743497969661599756933 1583576905869311549954425)
                      ·
                        rfl

theorem cell23_3084005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3084005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084005 prefixEnd_3084005 := by exact prefixLift 3084005
  have htrace : WordTrace (prefixWord ++ tailWord_3084005) baseStart_3084005 baseEnd_3084005 := by
    simpa [prefixWord, tailWord_3084005, baseEnd_3084005] using wordTrace_append hprefix tailTrace_3084005
  have hstable : (prefixWord ++ tailWord_3084005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084005).length < 2 ^ (prefixWord ++ tailWord_3084005).sum := by decide
  have hdescent : baseEnd_3084005 < baseStart_3084005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084012 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 3]
def baseStart_3084012 : Nat := 118140960795 + 3084012 * 2 ^ 59
def prefixEnd_3084012 : Nat := 4983230072969 + 3 ^ 40 * 3084012 * 2
def baseEnd_3084012 : Nat := 1583580500233893022566893

theorem tailTrace_3084012 : CollatzResearch.WordTrace tailWord_3084012 prefixEnd_3084012 1583580500233893022566893 := by
  unfold tailWord_3084012
  simp only [CollatzResearch.WordTrace]
  refine ⟨56241579251579353080699145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74988772335439137440932193 56241579251579353080699145)
  ·
    refine ⟨42181184438684514810524359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56241579251579353080699145 42181184438684514810524359)
    ·
      refine ⟨63271776658026772215786539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42181184438684514810524359 63271776658026772215786539)
      ·
        refine ⟨94907664987040158323679809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63271776658026772215786539 94907664987040158323679809)
        ·
          refine ⟨71180748740280118742759857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94907664987040158323679809 71180748740280118742759857)
          ·
            refine ⟨53385561555210089057069893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71180748740280118742759857 53385561555210089057069893)
            ·
              refine ⟨10009792791601891698200605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53385561555210089057069893 10009792791601891698200605)
              ·
                refine ⟨3753672296850709386825227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10009792791601891698200605 3753672296850709386825227)
                ·
                  refine ⟨5630508445276064080237841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753672296850709386825227 5630508445276064080237841)
                  ·
                    refine ⟨4222881333957048060178381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5630508445276064080237841 4222881333957048060178381)
                    ·
                      refine ⟨1583580500233893022566893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4222881333957048060178381 1583580500233893022566893)
                      ·
                        rfl

theorem cell23_3084012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_3084012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084012 prefixEnd_3084012 := by exact prefixLift 3084012
  have htrace : WordTrace (prefixWord ++ tailWord_3084012) baseStart_3084012 baseEnd_3084012 := by
    simpa [prefixWord, tailWord_3084012, baseEnd_3084012] using wordTrace_append hprefix tailTrace_3084012
  have hstable : (prefixWord ++ tailWord_3084012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084012).length < 2 ^ (prefixWord ++ tailWord_3084012).sum := by decide
  have hdescent : baseEnd_3084012 < baseStart_3084012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084036 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_3084036 : Nat := 118140960795 + 3084036 * 2 ^ 59
def prefixEnd_3084036 : Nat := 4983230072969 + 3 ^ 40 * 3084036 * 2
def baseEnd_3084036 : Nat := 527864274589866976222261

theorem tailTrace_3084036 : CollatzResearch.WordTrace tailWord_3084036 prefixEnd_3084036 527864274589866976222261 := by
  unfold tailWord_3084036
  simp only [CollatzResearch.WordTrace]
  refine ⟨56242016927535879130135981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74989355903381172173514641 56242016927535879130135981)
  ·
    refine ⟨21090756347825954673800993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56242016927535879130135981 21090756347825954673800993)
    ·
      refine ⟨15818067260869466005350745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21090756347825954673800993 15818067260869466005350745)
      ·
        refine ⟨11863550445652099504013059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15818067260869466005350745 11863550445652099504013059)
        ·
          refine ⟨17795325668478149256019589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11863550445652099504013059 17795325668478149256019589)
          ·
            refine ⟨3336623562839652985503673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17795325668478149256019589 3336623562839652985503673)
            ·
              refine ⟨2502467672129739739127755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3336623562839652985503673 2502467672129739739127755)
              ·
                refine ⟨3753701508194609608691633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502467672129739739127755 3753701508194609608691633)
                ·
                  refine ⟨2815276131145957206518725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3753701508194609608691633 2815276131145957206518725)
                  ·
                    refine ⟨527864274589866976222261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815276131145957206518725 527864274589866976222261)
                    ·
                      rfl

theorem cell23_3084036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_3084036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084036 prefixEnd_3084036 := by exact prefixLift 3084036
  have htrace : WordTrace (prefixWord ++ tailWord_3084036) baseStart_3084036 baseEnd_3084036 := by
    simpa [prefixWord, tailWord_3084036, baseEnd_3084036] using wordTrace_append hprefix tailTrace_3084036
  have hstable : (prefixWord ++ tailWord_3084036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084036).length < 2 ^ (prefixWord ++ tailWord_3084036).sum := by decide
  have hdescent : baseEnd_3084036 < baseStart_3084036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084086 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3084086 : Nat := 118140960795 + 3084086 * 2 ^ 59
def prefixEnd_3084086 : Nat := 4983230072969 + 3 ^ 40 * 3084086 * 2
def baseEnd_3084086 : Nat := 1583618497802325733041553

theorem tailTrace_3084086 : CollatzResearch.WordTrace tailWord_3084086 prefixEnd_3084086 1583618497802325733041553 := by
  unfold tailWord_3084086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7030366094055663549974507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74990571669927077866394741 7030366094055663549974507)
  ·
    refine ⟨10545549141083495324961761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7030366094055663549974507 10545549141083495324961761)
    ·
      refine ⟨7909161855812621493721321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10545549141083495324961761 7909161855812621493721321)
      ·
        refine ⟨5931871391859466120290991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7909161855812621493721321 5931871391859466120290991)
        ·
          refine ⟨8897807087789199180436487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5931871391859466120290991 8897807087789199180436487)
          ·
            refine ⟨13346710631683798770654731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8897807087789199180436487 13346710631683798770654731)
            ·
              refine ⟨20020065947525698155982097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13346710631683798770654731 20020065947525698155982097)
              ·
                refine ⟨15015049460644273616986573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20020065947525698155982097 15015049460644273616986573)
                ·
                  refine ⟨5630643547741602606369965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15015049460644273616986573 5630643547741602606369965)
                  ·
                    refine ⟨2111491330403100977388737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5630643547741602606369965 2111491330403100977388737)
                    ·
                      refine ⟨1583618497802325733041553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2111491330403100977388737 1583618497802325733041553)
                      ·
                        rfl

theorem cell23_3084086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3084086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084086 prefixEnd_3084086 := by exact prefixLift 3084086
  have htrace : WordTrace (prefixWord ++ tailWord_3084086) baseStart_3084086 baseEnd_3084086 := by
    simpa [prefixWord, tailWord_3084086, baseEnd_3084086] using wordTrace_append hprefix tailTrace_3084086
  have hstable : (prefixWord ++ tailWord_3084086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084086).length < 2 ^ (prefixWord ++ tailWord_3084086).sum := by decide
  have hdescent : baseEnd_3084086 < baseStart_3084086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084099 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 1, 4, 2]
def baseStart_3084099 : Nat := 118140960795 + 3084099 * 2 ^ 59
def prefixEnd_3084099 : Nat := 4983230072969 + 3 ^ 40 * 3084099 * 2
def baseEnd_3084099 : Nat := 1583625173050834182178993

theorem tailTrace_3084099 : CollatzResearch.WordTrace tailWord_3084099 prefixEnd_3084099 1583625173050834182178993 := by
  unfold tailWord_3084099
  simp only [CollatzResearch.WordTrace]
  refine ⟨112486331653843520019815351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74990887769229013346543567 112486331653843520019815351)
  ·
    refine ⟨168729497480765280029723027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112486331653843520019815351 168729497480765280029723027)
    ·
      refine ⟨253094246221147920044584541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168729497480765280029723027 253094246221147920044584541)
      ·
        refine ⟨94910342332930470016719203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253094246221147920044584541 94910342332930470016719203)
        ·
          refine ⟨142365513499395705025078805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94910342332930470016719203 142365513499395705025078805)
          ·
            refine ⟨6673383445284173673050569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142365513499395705025078805 6673383445284173673050569)
            ·
              refine ⟨5005037583963130254787927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6673383445284173673050569 5005037583963130254787927)
              ·
                refine ⟨7507556375944695382181891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5005037583963130254787927 7507556375944695382181891)
                ·
                  refine ⟨11261334563917043073272837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7507556375944695382181891 11261334563917043073272837)
                  ·
                    refine ⟨2111500230734445576238657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11261334563917043073272837 2111500230734445576238657)
                    ·
                      refine ⟨1583625173050834182178993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2111500230734445576238657 1583625173050834182178993)
                      ·
                        rfl

theorem cell23_3084099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_3084099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084099 prefixEnd_3084099 := by exact prefixLift 3084099
  have htrace : WordTrace (prefixWord ++ tailWord_3084099) baseStart_3084099 baseEnd_3084099 := by
    simpa [prefixWord, tailWord_3084099, baseEnd_3084099] using wordTrace_append hprefix tailTrace_3084099
  have hstable : (prefixWord ++ tailWord_3084099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084099).length < 2 ^ (prefixWord ++ tailWord_3084099).sum := by decide
  have hdescent : baseEnd_3084099 < baseStart_3084099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084105 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 7]
def baseStart_3084105 : Nat := 118140960795 + 3084105 * 2 ^ 59
def prefixEnd_3084105 : Nat := 4983230072969 + 3 ^ 40 * 3084105 * 2
def baseEnd_3084105 : Nat := 175958694881640128744885

theorem tailTrace_3084105 : CollatzResearch.WordTrace tailWord_3084105 prefixEnd_3084105 175958694881640128744885 := by
  unfold tailWord_3084105
  simp only [CollatzResearch.WordTrace]
  refine ⟨112486550491821783044533769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74991033661214522029689179 112486550491821783044533769)
  ·
    refine ⟨84364912868866337283400327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112486550491821783044533769 84364912868866337283400327)
    ·
      refine ⟨126547369303299505925100491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84364912868866337283400327 126547369303299505925100491)
      ·
        refine ⟨189821053954949258887650737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126547369303299505925100491 189821053954949258887650737)
        ·
          refine ⟨142365790466211944165738053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189821053954949258887650737 142365790466211944165738053)
          ·
            refine ⟨26693585712414739531075885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142365790466211944165738053 26693585712414739531075885)
            ·
              refine ⟨10010094642155527324153457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26693585712414739531075885 10010094642155527324153457)
              ·
                refine ⟨7507570981616645493115093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10010094642155527324153457 7507570981616645493115093)
                ·
                  refine ⟨175958694881640128744885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7507570981616645493115093 175958694881640128744885)
                  ·
                    rfl

theorem cell23_3084105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 7].length) (baseStart_3084105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084105 prefixEnd_3084105 := by exact prefixLift 3084105
  have htrace : WordTrace (prefixWord ++ tailWord_3084105) baseStart_3084105 baseEnd_3084105 := by
    simpa [prefixWord, tailWord_3084105, baseEnd_3084105] using wordTrace_append hprefix tailTrace_3084105
  have hstable : (prefixWord ++ tailWord_3084105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084105).length < 2 ^ (prefixWord ++ tailWord_3084105).sum := by decide
  have hdescent : baseEnd_3084105 < baseStart_3084105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084145 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_3084145 : Nat := 118140960795 + 3084145 * 2 ^ 59
def prefixEnd_3084145 : Nat := 4983230072969 + 3 ^ 40 * 3084145 * 2
def baseEnd_3084145 : Nat := 1583648793160941002203781

theorem tailTrace_3084145 : CollatzResearch.WordTrace tailWord_3084145 prefixEnd_3084145 1583648793160941002203781 := by
  unfold tailWord_3084145
  simp only [CollatzResearch.WordTrace]
  refine ⟨112488009411676869875989889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74992006274451246583993259 112488009411676869875989889)
  ·
    refine ⟨84366007058757652406992417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112488009411676869875989889 84366007058757652406992417)
    ·
      refine ⟨63274505294068239305244313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84366007058757652406992417 63274505294068239305244313)
      ·
        refine ⟨47455878970551179478933235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63274505294068239305244313 47455878970551179478933235)
        ·
          refine ⟨71183818455826769218399853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47455878970551179478933235 71183818455826769218399853)
          ·
            refine ⟨26693931920935038456899945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71183818455826769218399853 26693931920935038456899945)
            ·
              refine ⟨20020448940701278842674959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26693931920935038456899945 20020448940701278842674959)
              ·
                refine ⟨30030673411051918264012439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20020448940701278842674959 30030673411051918264012439)
                ·
                  refine ⟨45046010116577877396018659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30030673411051918264012439 45046010116577877396018659)
                  ·
                    refine ⟨67569015174866816094027989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45046010116577877396018659 67569015174866816094027989)
                    ·
                      refine ⟨1583648793160941002203781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67569015174866816094027989 1583648793160941002203781)
                      ·
                        rfl

theorem cell23_3084145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_3084145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084145 prefixEnd_3084145 := by exact prefixLift 3084145
  have htrace : WordTrace (prefixWord ++ tailWord_3084145) baseStart_3084145 baseEnd_3084145 := by
    simpa [prefixWord, tailWord_3084145, baseEnd_3084145] using wordTrace_append hprefix tailTrace_3084145
  have hstable : (prefixWord ++ tailWord_3084145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084145).length < 2 ^ (prefixWord ++ tailWord_3084145).sum := by decide
  have hdescent : baseEnd_3084145 < baseStart_3084145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084150 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3084150 : Nat := 118140960795 + 3084150 * 2 ^ 59
def prefixEnd_3084150 : Nat := 4983230072969 + 3 ^ 40 * 3084150 * 2
def baseEnd_3084150 : Nat := 1583651360564213482641259

theorem tailTrace_3084150 : CollatzResearch.WordTrace tailWord_3084150 prefixEnd_3084150 1583651360564213482641259 := by
  unfold tailWord_3084150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7030511986041172233120119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74992127851105837153281269 7030511986041172233120119)
  ·
    refine ⟨10545767979061758349680179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7030511986041172233120119 10545767979061758349680179)
    ·
      refine ⟨15818651968592637524520269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10545767979061758349680179 15818651968592637524520269)
      ·
        refine ⟨5931994488222239071695101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15818651968592637524520269 5931994488222239071695101)
        ·
          refine ⟨2224497933083339651885663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5931994488222239071695101 2224497933083339651885663)
          ·
            refine ⟨3336746899625009477828495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224497933083339651885663 3336746899625009477828495)
            ·
              refine ⟨5005120349437514216742743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336746899625009477828495 5005120349437514216742743)
              ·
                refine ⟨7507680524156271325114115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5005120349437514216742743 7507680524156271325114115)
                ·
                  refine ⟨11261520786234406987671173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7507680524156271325114115 11261520786234406987671173)
                  ·
                    refine ⟨2111535147418951310188345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11261520786234406987671173 2111535147418951310188345)
                    ·
                      refine ⟨1583651360564213482641259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2111535147418951310188345 1583651360564213482641259)
                      ·
                        rfl

theorem cell23_3084150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3084150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084150 prefixEnd_3084150 := by exact prefixLift 3084150
  have htrace : WordTrace (prefixWord ++ tailWord_3084150) baseStart_3084150 baseEnd_3084150 := by
    simpa [prefixWord, tailWord_3084150, baseEnd_3084150] using wordTrace_append hprefix tailTrace_3084150
  have hstable : (prefixWord ++ tailWord_3084150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084150).length < 2 ^ (prefixWord ++ tailWord_3084150).sum := by decide
  have hdescent : baseEnd_3084150 < baseStart_3084150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084165 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_3084165 : Nat := 118140960795 + 3084165 * 2 ^ 59
def prefixEnd_3084165 : Nat := 4983230072969 + 3 ^ 40 * 3084165 * 2
def baseEnd_3084165 : Nat := 527886354258010307984563

theorem tailTrace_3084165 : CollatzResearch.WordTrace tailWord_3084165 prefixEnd_3084165 527886354258010307984563 := by
  unfold tailWord_3084165
  simp only [CollatzResearch.WordTrace]
  refine ⟨112488738871604413291717949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74992492581069608861145299 112488738871604413291717949)
  ·
    refine ⟨42183277076851654984394231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112488738871604413291717949 42183277076851654984394231)
    ·
      refine ⟨63274915615277482476591347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42183277076851654984394231 63274915615277482476591347)
      ·
        refine ⟨94912373422916223714887021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63274915615277482476591347 94912373422916223714887021)
        ·
          refine ⟨35592140033593583893082633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94912373422916223714887021 35592140033593583893082633)
          ·
            refine ⟨26694105025195187919811975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35592140033593583893082633 26694105025195187919811975)
            ·
              refine ⟨40041157537792781879717963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26694105025195187919811975 40041157537792781879717963)
              ·
                refine ⟨60061736306689172819576945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40041157537792781879717963 60061736306689172819576945)
                ·
                  refine ⟨45046302230016879614682709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60061736306689172819576945 45046302230016879614682709)
                  ·
                    refine ⟨527886354258010307984563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45046302230016879614682709 527886354258010307984563)
                    ·
                      rfl

theorem cell23_3084165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_3084165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084165 prefixEnd_3084165 := by exact prefixLift 3084165
  have htrace : WordTrace (prefixWord ++ tailWord_3084165) baseStart_3084165 baseEnd_3084165 := by
    simpa [prefixWord, tailWord_3084165, baseEnd_3084165] using wordTrace_append hprefix tailTrace_3084165
  have hstable : (prefixWord ++ tailWord_3084165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084165).length < 2 ^ (prefixWord ++ tailWord_3084165).sum := by decide
  have hdescent : baseEnd_3084165 < baseStart_3084165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084172 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3084172 : Nat := 118140960795 + 3084172 * 2 ^ 59
def prefixEnd_3084172 : Nat := 4983230072969 + 3 ^ 40 * 3084172 * 2
def baseEnd_3084172 : Nat := 1583662657138612396566157

theorem tailTrace_3084172 : CollatzResearch.WordTrace tailWord_3084172 prefixEnd_3084172 1583662657138612396566157 := by
  unfold tailWord_3084172
  simp only [CollatzResearch.WordTrace]
  refine ⟨56244497091289526743611385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74992662788386035658148513 56244497091289526743611385)
  ·
    refine ⟨42183372818467145057708539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56244497091289526743611385 42183372818467145057708539)
    ·
      refine ⟨63275059227700717586562809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42183372818467145057708539 63275059227700717586562809)
      ·
        refine ⟨47456294420775538189922107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63275059227700717586562809 47456294420775538189922107)
        ·
          refine ⟨71184441631163307284883161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47456294420775538189922107 71184441631163307284883161)
          ·
            refine ⟨53388331223372480463662371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71184441631163307284883161 53388331223372480463662371)
            ·
              refine ⟨80082496835058720695493557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53388331223372480463662371 80082496835058720695493557)
              ·
                refine ⟨7507734078286755065202521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80082496835058720695493557 7507734078286755065202521)
                ·
                  refine ⟨5630800558715066298901891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7507734078286755065202521 5630800558715066298901891)
                  ·
                    refine ⟨8446200838072599448352837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5630800558715066298901891 8446200838072599448352837)
                    ·
                      refine ⟨1583662657138612396566157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8446200838072599448352837 1583662657138612396566157)
                      ·
                        rfl

theorem cell23_3084172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3084172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084172 prefixEnd_3084172 := by exact prefixLift 3084172
  have htrace : WordTrace (prefixWord ++ tailWord_3084172) baseStart_3084172 baseEnd_3084172 := by
    simpa [prefixWord, tailWord_3084172, baseEnd_3084172] using wordTrace_append hprefix tailTrace_3084172
  have hstable : (prefixWord ++ tailWord_3084172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084172).length < 2 ^ (prefixWord ++ tailWord_3084172).sum := by decide
  have hdescent : baseEnd_3084172 < baseStart_3084172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084185 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_3084185 : Nat := 118140960795 + 3084185 * 2 ^ 59
def prefixEnd_3084185 : Nat := 4983230072969 + 3 ^ 40 * 3084185 * 2
def baseEnd_3084185 : Nat := 1583669332387120845703597

theorem tailTrace_3084185 : CollatzResearch.WordTrace tailWord_3084185 prefixEnd_3084185 1583669332387120845703597 := by
  unfold tailWord_3084185
  simp only [CollatzResearch.WordTrace]
  refine ⟨112489468331531956707446009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74992978887687971138297339 112489468331531956707446009)
  ·
    refine ⟨84367101248648967530584507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112489468331531956707446009 84367101248648967530584507)
    ·
      refine ⟨126550651872973451295876761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84367101248648967530584507 126550651872973451295876761)
      ·
        refine ⟨94912988904730088471907571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126550651872973451295876761 94912988904730088471907571)
        ·
          refine ⟨142369483357095132707861357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94912988904730088471907571 142369483357095132707861357)
          ·
            refine ⟨53388556258910674765448009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142369483357095132707861357 53388556258910674765448009)
            ·
              refine ⟨40041417194183006074086007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53388556258910674765448009 40041417194183006074086007)
              ·
                refine ⟨60062125791274509111129011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40041417194183006074086007 60062125791274509111129011)
                ·
                  refine ⟨90093188686911763666693517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60062125791274509111129011 90093188686911763666693517)
                  ·
                    refine ⟨33784945757591911375010069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90093188686911763666693517 33784945757591911375010069)
                    ·
                      refine ⟨1583669332387120845703597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33784945757591911375010069 1583669332387120845703597)
                      ·
                        rfl

theorem cell23_3084185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_3084185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084185 prefixEnd_3084185 := by exact prefixLift 3084185
  have htrace : WordTrace (prefixWord ++ tailWord_3084185) baseStart_3084185 baseEnd_3084185 := by
    simpa [prefixWord, tailWord_3084185, baseEnd_3084185] using wordTrace_append hprefix tailTrace_3084185
  have hstable : (prefixWord ++ tailWord_3084185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084185).length < 2 ^ (prefixWord ++ tailWord_3084185).sum := by decide
  have hdescent : baseEnd_3084185 < baseStart_3084185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084189 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_3084189 : Nat := 118140960795 + 3084189 * 2 ^ 59
def prefixEnd_3084189 : Nat := 4983230072969 + 3 ^ 40 * 3084189 * 2
def baseEnd_3084189 : Nat := 1583671386309738830053579

theorem tailTrace_3084189 : CollatzResearch.WordTrace tailWord_3084189 prefixEnd_3084189 1583671386309738830053579 := by
  unfold tailWord_3084189
  simp only [CollatzResearch.WordTrace]
  refine ⟨112489614223517465390591621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74993076149011643593727747 112489614223517465390591621)
  ·
    refine ⟨21091802666909524760735929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112489614223517465390591621 21091802666909524760735929)
    ·
      refine ⟨15818852000182143570551947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21091802666909524760735929 15818852000182143570551947)
      ·
        refine ⟨23728278000273215355827921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15818852000182143570551947 23728278000273215355827921)
        ·
          refine ⟨17796208500204911516870941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23728278000273215355827921 17796208500204911516870941)
          ·
            refine ⟨6673578187576841818826603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17796208500204911516870941 6673578187576841818826603)
            ·
              refine ⟨10010367281365262728239905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6673578187576841818826603 10010367281365262728239905)
              ·
                refine ⟨7507775461023947046179929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10010367281365262728239905 7507775461023947046179929)
                ·
                  refine ⟨5630831595767960284634947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7507775461023947046179929 5630831595767960284634947)
                  ·
                    refine ⟨8446247393651940426952421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5630831595767960284634947 8446247393651940426952421)
                    ·
                      refine ⟨1583671386309738830053579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8446247393651940426952421 1583671386309738830053579)
                      ·
                        rfl

theorem cell23_3084189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_3084189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084189 prefixEnd_3084189 := by exact prefixLift 3084189
  have htrace : WordTrace (prefixWord ++ tailWord_3084189) baseStart_3084189 baseEnd_3084189 := by
    simpa [prefixWord, tailWord_3084189, baseEnd_3084189] using wordTrace_append hprefix tailTrace_3084189
  have hstable : (prefixWord ++ tailWord_3084189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084189).length < 2 ^ (prefixWord ++ tailWord_3084189).sum := by decide
  have hdescent : baseEnd_3084189 < baseStart_3084189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084190 : List Nat := [4, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3084190 : Nat := 118140960795 + 3084190 * 2 ^ 59
def prefixEnd_3084190 : Nat := 4983230072969 + 3 ^ 40 * 3084190 * 2
def baseEnd_3084190 : Nat := 175963544421154814015675

theorem tailTrace_3084190 : CollatzResearch.WordTrace tailWord_3084190 prefixEnd_3084190 175963544421154814015675 := by
  unfold tailWord_3084190
  simp only [CollatzResearch.WordTrace]
  refine ⟨14061206337064230320172253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74993100464342561707585349 14061206337064230320172253)
  ·
    refine ⟨5272952376399086370064595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14061206337064230320172253 5272952376399086370064595)
    ·
      refine ⟨7909428564598629555096893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5272952376399086370064595 7909428564598629555096893)
      ·
        refine ⟨2966035711724486083161335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7909428564598629555096893 2966035711724486083161335)
        ·
          refine ⟨4449053567586729124742003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966035711724486083161335 4449053567586729124742003)
          ·
            refine ⟨6673580351380093687113005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449053567586729124742003 6673580351380093687113005)
            ·
              refine ⟨2502592631767535132667377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6673580351380093687113005 2502592631767535132667377)
              ·
                refine ⟨1876944473825651349500533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502592631767535132667377 1876944473825651349500533)
                ·
                  refine ⟨175963544421154814015675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1876944473825651349500533 175963544421154814015675)
                  ·
                    rfl

theorem cell23_3084190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3084190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084190 prefixEnd_3084190 := by exact prefixLift 3084190
  have htrace : WordTrace (prefixWord ++ tailWord_3084190) baseStart_3084190 baseEnd_3084190 := by
    simpa [prefixWord, tailWord_3084190, baseEnd_3084190] using wordTrace_append hprefix tailTrace_3084190
  have hstable : (prefixWord ++ tailWord_3084190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084190).length < 2 ^ (prefixWord ++ tailWord_3084190).sum := by decide
  have hdescent : baseEnd_3084190 < baseStart_3084190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084250 : List Nat := [3, 1, 1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_3084250 : Nat := 118140960795 + 3084250 * 2 ^ 59
def prefixEnd_3084250 : Nat := 4983230072969 + 3 ^ 40 * 3084250 * 2
def baseEnd_3084250 : Nat := 527900902876554363796933

theorem tailTrace_3084250 : CollatzResearch.WordTrace tailWord_3084250 prefixEnd_3084250 527900902876554363796933 := by
  unfold tailWord_3084250
  simp only [CollatzResearch.WordTrace]
  refine ⟨28122959769074118202140551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74994559384197648539041469 28122959769074118202140551)
  ·
    refine ⟨42184439653611177303210827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28122959769074118202140551 42184439653611177303210827)
    ·
      refine ⟨63276659480416765954816241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42184439653611177303210827 63276659480416765954816241)
      ·
        refine ⟨47457494610312574466112181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63276659480416765954816241 47457494610312574466112181)
        ·
          refine ⟨4449140119716803856198017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47457494610312574466112181 4449140119716803856198017)
          ·
            refine ⟨3336855089787602892148513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4449140119716803856198017 3336855089787602892148513)
            ·
              refine ⟨2502641317340702169111385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3336855089787602892148513 2502641317340702169111385)
              ·
                refine ⟨1876980988005526626833539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502641317340702169111385 1876980988005526626833539)
                ·
                  refine ⟨2815471482008289940250309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876980988005526626833539 2815471482008289940250309)
                  ·
                    refine ⟨527900902876554363796933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815471482008289940250309 527900902876554363796933)
                    ·
                      rfl

theorem cell23_3084250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_3084250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084250 prefixEnd_3084250 := by exact prefixLift 3084250
  have htrace : WordTrace (prefixWord ++ tailWord_3084250) baseStart_3084250 baseEnd_3084250 := by
    simpa [prefixWord, tailWord_3084250, baseEnd_3084250] using wordTrace_append hprefix tailTrace_3084250
  have hstable : (prefixWord ++ tailWord_3084250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084250).length < 2 ^ (prefixWord ++ tailWord_3084250).sum := by decide
  have hdescent : baseEnd_3084250 < baseStart_3084250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084272 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 1, 6]
def baseStart_3084272 : Nat := 118140960795 + 3084272 * 2 ^ 59
def prefixEnd_3084272 : Nat := 4983230072969 + 3 ^ 40 * 3084272 * 2
def baseEnd_3084272 : Nat := 527904668401354001771899

theorem tailTrace_3084272 : CollatzResearch.WordTrace tailWord_3084272 prefixEnd_3084272 527904668401354001771899 := by
  unfold tailWord_3084272
  simp only [CollatzResearch.WordTrace]
  refine ⟨56246320741108385282931535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74995094321477847043908713 56246320741108385282931535)
  ·
    refine ⟨84369481111662577924397303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56246320741108385282931535 84369481111662577924397303)
    ·
      refine ⟨126554221667493866886595955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84369481111662577924397303 126554221667493866886595955)
      ·
        refine ⟨189831332501240800329893933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126554221667493866886595955 189831332501240800329893933)
        ·
          refine ⟨71186749687965300123710225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189831332501240800329893933 71186749687965300123710225)
          ·
            refine ⟨53390062265973975092782669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71186749687965300123710225 53390062265973975092782669)
            ·
              refine ⟨20021273349740240659793501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53390062265973975092782669 20021273349740240659793501)
              ·
                refine ⟨7507977506152590247422563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20021273349740240659793501 7507977506152590247422563)
                ·
                  refine ⟨11261966259228885371133845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7507977506152590247422563 11261966259228885371133845)
                  ·
                    refine ⟨527904668401354001771899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11261966259228885371133845 527904668401354001771899)
                    ·
                      rfl

theorem cell23_3084272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_3084272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084272 prefixEnd_3084272 := by exact prefixLift 3084272
  have htrace : WordTrace (prefixWord ++ tailWord_3084272) baseStart_3084272 baseEnd_3084272 := by
    simpa [prefixWord, tailWord_3084272, baseEnd_3084272] using wordTrace_append hprefix tailTrace_3084272
  have hstable : (prefixWord ++ tailWord_3084272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084272).length < 2 ^ (prefixWord ++ tailWord_3084272).sum := by decide
  have hdescent : baseEnd_3084272 < baseStart_3084272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084289 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 4, 4]
def baseStart_3084289 : Nat := 118140960795 + 3084289 * 2 ^ 59
def prefixEnd_3084289 : Nat := 4983230072969 + 3 ^ 40 * 3084289 * 2
def baseEnd_3084289 : Nat := 527907578125062812934373

theorem tailTrace_3084289 : CollatzResearch.WordTrace tailWord_3084289 prefixEnd_3084289 527907578125062812934373 := by
  unfold tailWord_3084289
  simp only [CollatzResearch.WordTrace]
  refine ⟨112493261523155182469231921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74995507682103454979487947 112493261523155182469231921)
  ·
    refine ⟨84369946142366386851923941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112493261523155182469231921 84369946142366386851923941)
    ·
      refine ⟨15819364901693697534735739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84369946142366386851923941 15819364901693697534735739)
      ·
        refine ⟨23729047352540546302103609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15819364901693697534735739 23729047352540546302103609)
        ·
          refine ⟨17796785514405409726577707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23729047352540546302103609 17796785514405409726577707)
          ·
            refine ⟨26695178271608114589866561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17796785514405409726577707 26695178271608114589866561)
            ·
              refine ⟨20021383703706085942399921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26695178271608114589866561 20021383703706085942399921)
              ·
                refine ⟨15016037777779564456799941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20021383703706085942399921 15016037777779564456799941)
                ·
                  refine ⟨2815507083333668335649989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15016037777779564456799941 2815507083333668335649989)
                  ·
                    refine ⟨527907578125062812934373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815507083333668335649989 527907578125062812934373)
                    ·
                      rfl

theorem cell23_3084289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_3084289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084289 prefixEnd_3084289 := by exact prefixLift 3084289
  have htrace : WordTrace (prefixWord ++ tailWord_3084289) baseStart_3084289 baseEnd_3084289 := by
    simpa [prefixWord, tailWord_3084289, baseEnd_3084289] using wordTrace_append hprefix tailTrace_3084289
  have hstable : (prefixWord ++ tailWord_3084289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084289).length < 2 ^ (prefixWord ++ tailWord_3084289).sum := by decide
  have hdescent : baseEnd_3084289 < baseStart_3084289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084296 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_3084296 : Nat := 118140960795 + 3084296 * 2 ^ 59
def prefixEnd_3084296 : Nat := 4983230072969 + 3 ^ 40 * 3084296 * 2
def baseEnd_3084296 : Nat := 1583726328739769911415587

theorem tailTrace_3084296 : CollatzResearch.WordTrace tailWord_3084296 prefixEnd_3084296 1583726328739769911415587 := by
  unfold tailWord_3084296
  simp only [CollatzResearch.WordTrace]
  refine ⟨56246758417064911332368371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74995677889419881776491161 56246758417064911332368371)
  ·
    refine ⟨84370137625597366998552557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56246758417064911332368371 84370137625597366998552557)
    ·
      refine ⟨31638801609599012624457209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84370137625597366998552557 31638801609599012624457209)
      ·
        refine ⟨23729101207199259468342907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31638801609599012624457209 23729101207199259468342907)
        ·
          refine ⟨35593651810798889202514361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23729101207199259468342907 35593651810798889202514361)
          ·
            refine ⟨26695238858099166901885771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35593651810798889202514361 26695238858099166901885771)
            ·
              refine ⟨40042858287148750352828657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26695238858099166901885771 40042858287148750352828657)
              ·
                refine ⟨30032143715361562764621493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40042858287148750352828657 30032143715361562764621493)
                ·
                  refine ⟨2815513473315146509183265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30032143715361562764621493 2815513473315146509183265)
                  ·
                    refine ⟨2111635104986359881887449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2815513473315146509183265 2111635104986359881887449)
                    ·
                      refine ⟨1583726328739769911415587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2111635104986359881887449 1583726328739769911415587)
                      ·
                        rfl

theorem cell23_3084296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_3084296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084296 prefixEnd_3084296 := by exact prefixLift 3084296
  have htrace : WordTrace (prefixWord ++ tailWord_3084296) baseStart_3084296 baseEnd_3084296 := by
    simpa [prefixWord, tailWord_3084296, baseEnd_3084296] using wordTrace_append hprefix tailTrace_3084296
  have hstable : (prefixWord ++ tailWord_3084296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084296).length < 2 ^ (prefixWord ++ tailWord_3084296).sum := by decide
  have hdescent : baseEnd_3084296 < baseStart_3084296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084302 : List Nat := [4, 1, 1, 2, 2, 1, 12]
def baseStart_3084302 : Nat := 118140960795 + 3084302 * 2 ^ 59
def prefixEnd_3084302 : Nat := 4983230072969 + 3 ^ 40 * 3084302 * 2
def baseEnd_3084302 : Nat := 19552214933625887505439

theorem tailTrace_3084302 : CollatzResearch.WordTrace tailWord_3084302 prefixEnd_3084302 19552214933625887505439 := by
  unfold tailWord_3084302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14061716959013510711181895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74995823781405390459636773 14061716959013510711181895)
  ·
    refine ⟨21092575438520266066772843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14061716959013510711181895 21092575438520266066772843)
    ·
      refine ⟨31638863157780399100159265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21092575438520266066772843 31638863157780399100159265)
      ·
        refine ⟨23729147368335299325119449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31638863157780399100159265 23729147368335299325119449)
        ·
          refine ⟨17796860526251474493839587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23729147368335299325119449 17796860526251474493839587)
          ·
            refine ⟨26695290789377211740759381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17796860526251474493839587 26695290789377211740759381)
            ·
              refine ⟨19552214933625887505439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 26695290789377211740759381 19552214933625887505439)
              ·
                rfl

theorem cell23_3084302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 12].length) (baseStart_3084302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084302 prefixEnd_3084302 := by exact prefixLift 3084302
  have htrace : WordTrace (prefixWord ++ tailWord_3084302) baseStart_3084302 baseEnd_3084302 := by
    simpa [prefixWord, tailWord_3084302, baseEnd_3084302] using wordTrace_append hprefix tailTrace_3084302
  have hstable : (prefixWord ++ tailWord_3084302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084302).length < 2 ^ (prefixWord ++ tailWord_3084302).sum := by decide
  have hdescent : baseEnd_3084302 < baseStart_3084302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084380 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_3084380 : Nat := 118140960795 + 3084380 * 2 ^ 59
def prefixEnd_3084380 : Nat := 4983230072969 + 3 ^ 40 * 3084380 * 2
def baseEnd_3084380 : Nat := 1583769461114747582765201

theorem tailTrace_3084380 : CollatzResearch.WordTrace tailWord_3084380 prefixEnd_3084380 1583769461114747582765201 := by
  unfold tailWord_3084380
  simp only [CollatzResearch.WordTrace]
  refine ⟨56248290282912752505397297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74997720377217003340529729 56248290282912752505397297)
  ·
    refine ⟨42186217712184564379047973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56248290282912752505397297 42186217712184564379047973)
    ·
      refine ⟨7909915821034605821071495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42186217712184564379047973 7909915821034605821071495)
      ·
        refine ⟨11864873731551908731607243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7909915821034605821071495 11864873731551908731607243)
        ·
          refine ⟨17797310597327863097410865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11864873731551908731607243 17797310597327863097410865)
          ·
            refine ⟨13347982947995897323058149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17797310597327863097410865 13347982947995897323058149)
            ·
              refine ⟨2502746802749230748073403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13347982947995897323058149 2502746802749230748073403)
              ·
                refine ⟨3754120204123846122110105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502746802749230748073403 3754120204123846122110105)
                ·
                  refine ⟨2815590153092884591582579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3754120204123846122110105 2815590153092884591582579)
                  ·
                    refine ⟨4223385229639326887373869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2815590153092884591582579 4223385229639326887373869)
                    ·
                      refine ⟨1583769461114747582765201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4223385229639326887373869 1583769461114747582765201)
                      ·
                        rfl

theorem cell23_3084380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_3084380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084380 prefixEnd_3084380 := by exact prefixLift 3084380
  have htrace : WordTrace (prefixWord ++ tailWord_3084380) baseStart_3084380 baseEnd_3084380 := by
    simpa [prefixWord, tailWord_3084380, baseEnd_3084380] using wordTrace_append hprefix tailTrace_3084380
  have hstable : (prefixWord ++ tailWord_3084380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084380).length < 2 ^ (prefixWord ++ tailWord_3084380).sum := by decide
  have hdescent : baseEnd_3084380 < baseStart_3084380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084389 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3084389 : Nat := 118140960795 + 3084389 * 2 ^ 59
def prefixEnd_3084389 : Nat := 4983230072969 + 3 ^ 40 * 3084389 * 2
def baseEnd_3084389 : Nat := 1583774082440638047552659

theorem tailTrace_3084389 : CollatzResearch.WordTrace tailWord_3084389 prefixEnd_3084389 1583774082440638047552659 := by
  unfold tailWord_3084389
  simp only [CollatzResearch.WordTrace]
  refine ⟨112496908822792899547872221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74997939215195266365248147 112496908822792899547872221)
  ·
    refine ⟨42186340808547337330452083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112496908822792899547872221 42186340808547337330452083)
    ·
      refine ⟨63279511212821005995678125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42186340808547337330452083 63279511212821005995678125)
      ·
        refine ⟨23729816704807877248379297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63279511212821005995678125 23729816704807877248379297)
        ·
          refine ⟨17797362528605907936284473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23729816704807877248379297 17797362528605907936284473)
          ·
            refine ⟨13348021896454430952213355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17797362528605907936284473 13348021896454430952213355)
            ·
              refine ⟨20022032844681646428320033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13348021896454430952213355 20022032844681646428320033)
              ·
                refine ⟨15016524633511234821240025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20022032844681646428320033 15016524633511234821240025)
                ·
                  refine ⟨11262393475133426115930019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15016524633511234821240025 11262393475133426115930019)
                  ·
                    refine ⟨16893590212700139173895029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11262393475133426115930019 16893590212700139173895029)
                    ·
                      refine ⟨1583774082440638047552659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16893590212700139173895029 1583774082440638047552659)
                      ·
                        rfl

theorem cell23_3084389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3084389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084389 prefixEnd_3084389 := by exact prefixLift 3084389
  have htrace : WordTrace (prefixWord ++ tailWord_3084389) baseStart_3084389 baseEnd_3084389 := by
    simpa [prefixWord, tailWord_3084389, baseEnd_3084389] using wordTrace_append hprefix tailTrace_3084389
  have hstable : (prefixWord ++ tailWord_3084389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084389).length < 2 ^ (prefixWord ++ tailWord_3084389).sum := by decide
  have hdescent : baseEnd_3084389 < baseStart_3084389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084406 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3084406 : Nat := 118140960795 + 3084406 * 2 ^ 59
def prefixEnd_3084406 : Nat := 4983230072969 + 3 ^ 40 * 3084406 * 2
def baseEnd_3084406 : Nat := 1583782811611764481040081

theorem tailTrace_3084406 : CollatzResearch.WordTrace tailWord_3084406 prefixEnd_3084406 1583782811611764481040081 := by
  unfold tailWord_3084406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031095553983206965702567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74998352575820874300827381 7031095553983206965702567)
  ·
    refine ⟨10546643330974810448553851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7031095553983206965702567 10546643330974810448553851)
    ·
      refine ⟨15819964996462215672830777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10546643330974810448553851 15819964996462215672830777)
      ·
        refine ⟨11864973747346661754623083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15819964996462215672830777 11864973747346661754623083)
        ·
          refine ⟨17797460621019992631934625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11864973747346661754623083 17797460621019992631934625)
          ·
            refine ⟨13348095465764994473950969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17797460621019992631934625 13348095465764994473950969)
            ·
              refine ⟨10011071599323745855463227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13348095465764994473950969 10011071599323745855463227)
              ·
                refine ⟨15016607398985618783194841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10011071599323745855463227 15016607398985618783194841)
                ·
                  refine ⟨11262455549239214087396131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15016607398985618783194841 11262455549239214087396131)
                  ·
                    refine ⟨16893683323858821131094197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11262455549239214087396131 16893683323858821131094197)
                    ·
                      refine ⟨1583782811611764481040081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16893683323858821131094197 1583782811611764481040081)
                      ·
                        rfl

theorem cell23_3084406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3084406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084406 prefixEnd_3084406 := by exact prefixLift 3084406
  have htrace : WordTrace (prefixWord ++ tailWord_3084406) baseStart_3084406 baseEnd_3084406 := by
    simpa [prefixWord, tailWord_3084406, baseEnd_3084406] using wordTrace_append hprefix tailTrace_3084406
  have hstable : (prefixWord ++ tailWord_3084406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084406).length < 2 ^ (prefixWord ++ tailWord_3084406).sum := by decide
  have hdescent : baseEnd_3084406 < baseStart_3084406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084420 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_3084420 : Nat := 118140960795 + 3084420 * 2 ^ 59
def prefixEnd_3084420 : Nat := 4983230072969 + 3 ^ 40 * 3084420 * 2
def baseEnd_3084420 : Nat := 1583790000340927426265017

theorem tailTrace_3084420 : CollatzResearch.WordTrace tailWord_3084420 prefixEnd_3084420 1583790000340927426265017 := by
  unfold tailWord_3084420
  simp only [CollatzResearch.WordTrace]
  refine ⟨56249019742840295921125357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74998692990453727894833809 56249019742840295921125357)
  ·
    refine ⟨21093382403565110970422009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56249019742840295921125357 21093382403565110970422009)
    ·
      refine ⟨15820036802673833227816507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21093382403565110970422009 15820036802673833227816507)
      ·
        refine ⟨23730055204010749841724761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15820036802673833227816507 23730055204010749841724761)
        ·
          refine ⟨17797541403008062381293571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23730055204010749841724761 17797541403008062381293571)
          ·
            refine ⟨26696312104512093571940357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17797541403008062381293571 26696312104512093571940357)
            ·
              refine ⟨5005558519596017544738817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26696312104512093571940357 5005558519596017544738817)
              ·
                refine ⟨3754168889697013158554113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5005558519596017544738817 3754168889697013158554113)
                ·
                  refine ⟨2815626667272759868915585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3754168889697013158554113 2815626667272759868915585)
                  ·
                    refine ⟨2111720000454569901686689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2815626667272759868915585 2111720000454569901686689)
                    ·
                      refine ⟨1583790000340927426265017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2111720000454569901686689 1583790000340927426265017)
                      ·
                        rfl

theorem cell23_3084420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_3084420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084420 prefixEnd_3084420 := by exact prefixLift 3084420
  have htrace : WordTrace (prefixWord ++ tailWord_3084420) baseStart_3084420 baseEnd_3084420 := by
    simpa [prefixWord, tailWord_3084420, baseEnd_3084420] using wordTrace_append hprefix tailTrace_3084420
  have hstable : (prefixWord ++ tailWord_3084420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084420).length < 2 ^ (prefixWord ++ tailWord_3084420).sum := by decide
  have hdescent : baseEnd_3084420 < baseStart_3084420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084520 : List Nat := [2, 1, 4, 1, 2, 2, 3, 3, 1, 4]
def baseStart_3084520 : Nat := 118140960795 + 3084520 * 2 ^ 59
def prefixEnd_3084520 : Nat := 4983230072969 + 3 ^ 40 * 3084520 * 2
def baseEnd_3084520 : Nat := 527947116135459011671519

theorem tailTrace_3084520 : CollatzResearch.WordTrace tailWord_3084520 prefixEnd_3084520 527947116135459011671519 := by
  unfold tailWord_3084520
  simp only [CollatzResearch.WordTrace]
  refine ⟨56250843392659154460445507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75001124523545539280594009 56250843392659154460445507)
  ·
    refine ⟨84376265088988731690668261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56250843392659154460445507 84376265088988731690668261)
    ·
      refine ⟨15820549704185387192000299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84376265088988731690668261 15820549704185387192000299)
      ·
        refine ⟨23730824556278080788000449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15820549704185387192000299 23730824556278080788000449)
        ·
          refine ⟨17798118417208560591000337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23730824556278080788000449 17798118417208560591000337)
          ·
            refine ⟨13348588812906420443250253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17798118417208560591000337 13348588812906420443250253)
            ·
              refine ⟨5005720804839907666218845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13348588812906420443250253 5005720804839907666218845)
              ·
                refine ⟨1877145301814965374832067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5005720804839907666218845 1877145301814965374832067)
                ·
                  refine ⟨2815717952722448062248101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877145301814965374832067 2815717952722448062248101)
                  ·
                    refine ⟨527947116135459011671519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815717952722448062248101 527947116135459011671519)
                    ·
                      rfl

theorem cell23_3084520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_3084520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084520 prefixEnd_3084520 := by exact prefixLift 3084520
  have htrace : WordTrace (prefixWord ++ tailWord_3084520) baseStart_3084520 baseEnd_3084520 := by
    simpa [prefixWord, tailWord_3084520, baseEnd_3084520] using wordTrace_append hprefix tailTrace_3084520
  have hstable : (prefixWord ++ tailWord_3084520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084520).length < 2 ^ (prefixWord ++ tailWord_3084520).sum := by decide
  have hdescent : baseEnd_3084520 < baseStart_3084520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084559 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 5, 6]
def baseStart_3084559 : Nat := 118140960795 + 3084559 * 2 ^ 59
def prefixEnd_3084559 : Nat := 4983230072969 + 3 ^ 40 * 3084559 * 2
def baseEnd_3084559 : Nat := 527953791383967460808959

theorem tailTrace_3084559 : CollatzResearch.WordTrace tailWord_3084559 prefixEnd_3084559 527953791383967460808959 := by
  unfold tailWord_3084559
  simp only [CollatzResearch.WordTrace]
  refine ⟨112503109232177018581560731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75002072821451345721040487 112503109232177018581560731)
  ·
    refine ⟨168754663848265527872341097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112503109232177018581560731 168754663848265527872341097)
    ·
      refine ⟨126565997886199145904255823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168754663848265527872341097 126565997886199145904255823)
      ·
        refine ⟨189848996829298718856383735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126565997886199145904255823 189848996829298718856383735)
        ·
          refine ⟨284773495243948078284575603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189848996829298718856383735 284773495243948078284575603)
          ·
            refine ⟨427160242865922117426863405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284773495243948078284575603 427160242865922117426863405)
            ·
              refine ⟨160185091074720794035073777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427160242865922117426863405 160185091074720794035073777)
              ·
                refine ⟨120138818306040595526305333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160185091074720794035073777 120138818306040595526305333)
                ·
                  refine ⟨11263014216191305830591125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120138818306040595526305333 11263014216191305830591125)
                  ·
                    refine ⟨527953791383967460808959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11263014216191305830591125 527953791383967460808959)
                    ·
                      rfl

theorem cell23_3084559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_3084559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084559 prefixEnd_3084559 := by exact prefixLift 3084559
  have htrace : WordTrace (prefixWord ++ tailWord_3084559) baseStart_3084559 baseEnd_3084559 := by
    simpa [prefixWord, tailWord_3084559, baseEnd_3084559] using wordTrace_append hprefix tailTrace_3084559
  have hstable : (prefixWord ++ tailWord_3084559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084559).length < 2 ^ (prefixWord ++ tailWord_3084559).sum := by decide
  have hdescent : baseEnd_3084559 < baseStart_3084559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084569 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_3084569 : Nat := 118140960795 + 3084569 * 2 ^ 59
def prefixEnd_3084569 : Nat := 4983230072969 + 3 ^ 40 * 3084569 * 2
def baseEnd_3084569 : Nat := 1583866508958447343301831

theorem tailTrace_3084569 : CollatzResearch.WordTrace tailWord_3084569 prefixEnd_3084569 1583866508958447343301831 := by
  unfold tailWord_3084569
  simp only [CollatzResearch.WordTrace]
  refine ⟨112503473962140790289424761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75002315974760526859616507 112503473962140790289424761)
  ·
    refine ⟨84377605471605592717068571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112503473962140790289424761 84377605471605592717068571)
    ·
      refine ⟨126566408207408389075602857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84377605471605592717068571 126566408207408389075602857)
      ·
        refine ⟨94924806155556291806702143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126566408207408389075602857 94924806155556291806702143)
        ·
          refine ⟨142387209233334437710053215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94924806155556291806702143 142387209233334437710053215)
          ·
            refine ⟨213580813850001656565079823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142387209233334437710053215 213580813850001656565079823)
            ·
              refine ⟨320371220775002484847619735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213580813850001656565079823 320371220775002484847619735)
              ·
                refine ⟨480556831162503727271429603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320371220775002484847619735 480556831162503727271429603)
                ·
                  refine ⟨720835246743755590907144405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480556831162503727271429603 720835246743755590907144405)
                  ·
                    refine ⟨16894576095556771661886197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 720835246743755590907144405 16894576095556771661886197)
                    ·
                      refine ⟨1583866508958447343301831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16894576095556771661886197 1583866508958447343301831)
                      ·
                        rfl

theorem cell23_3084569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_3084569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084569 prefixEnd_3084569 := by exact prefixLift 3084569
  have htrace : WordTrace (prefixWord ++ tailWord_3084569) baseStart_3084569 baseEnd_3084569 := by
    simpa [prefixWord, tailWord_3084569, baseEnd_3084569] using wordTrace_append hprefix tailTrace_3084569
  have hstable : (prefixWord ++ tailWord_3084569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084569).length < 2 ^ (prefixWord ++ tailWord_3084569).sum := by decide
  have hdescent : baseEnd_3084569 < baseStart_3084569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084576 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 3, 6]
def baseStart_3084576 : Nat := 118140960795 + 3084576 * 2 ^ 59
def prefixEnd_3084576 : Nat := 4983230072969 + 3 ^ 40 * 3084576 * 2
def baseEnd_3084576 : Nat := 527956701107676271971433

theorem tailTrace_3084576 : CollatzResearch.WordTrace tailWord_3084576 prefixEnd_3084576 527956701107676271971433 := by
  unfold tailWord_3084576
  simp only [CollatzResearch.WordTrace]
  refine ⟨56251864636557715242464791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75002486182076953656619721 56251864636557715242464791)
  ·
    refine ⟨84377796954836572863697187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56251864636557715242464791 84377796954836572863697187)
    ·
      refine ⟨126566695432254859295545781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84377796954836572863697187 126566695432254859295545781)
      ·
        refine ⟨11865627696773893058957417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126566695432254859295545781 11865627696773893058957417)
        ·
          refine ⟨8899220772580419794218063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11865627696773893058957417 8899220772580419794218063)
          ·
            refine ⟨13348831158870629691327095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8899220772580419794218063 13348831158870629691327095)
            ·
              refine ⟨20023246738305944536990643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13348831158870629691327095 20023246738305944536990643)
              ·
                refine ⟨30034870107458916805485965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20023246738305944536990643 30034870107458916805485965)
                ·
                  refine ⟨11263076290297093802057237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30034870107458916805485965 11263076290297093802057237)
                  ·
                    refine ⟨527956701107676271971433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11263076290297093802057237 527956701107676271971433)
                    ·
                      rfl

theorem cell23_3084576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_3084576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084576 prefixEnd_3084576 := by exact prefixLift 3084576
  have htrace : WordTrace (prefixWord ++ tailWord_3084576) baseStart_3084576 baseEnd_3084576 := by
    simpa [prefixWord, tailWord_3084576, baseEnd_3084576] using wordTrace_append hprefix tailTrace_3084576
  have hstable : (prefixWord ++ tailWord_3084576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084576).length < 2 ^ (prefixWord ++ tailWord_3084576).sum := by decide
  have hdescent : baseEnd_3084576 < baseStart_3084576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084580 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_3084580 : Nat := 118140960795 + 3084580 * 2 ^ 59
def prefixEnd_3084580 : Nat := 4983230072969 + 3 ^ 40 * 3084580 * 2
def baseEnd_3084580 : Nat := 527957385748548933421427

theorem tailTrace_3084580 : CollatzResearch.WordTrace tailWord_3084580 prefixEnd_3084580 527957385748548933421427 := by
  unfold tailWord_3084580
  simp only [CollatzResearch.WordTrace]
  refine ⟨56251937582550469584037597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75002583443400626112050129 56251937582550469584037597)
  ·
    refine ⟨21094476593456426094014099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56251937582550469584037597 21094476593456426094014099)
    ·
      refine ⟨31641714890184639141021149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21094476593456426094014099 31641714890184639141021149)
      ·
        refine ⟨11865643083819239677882931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31641714890184639141021149 11865643083819239677882931)
        ·
          refine ⟨17798464625728859516824397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11865643083819239677882931 17798464625728859516824397)
          ·
            refine ⟨6674424234648322318809149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17798464625728859516824397 6674424234648322318809149)
            ·
              refine ⟨2502909087993120869553431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6674424234648322318809149 2502909087993120869553431)
              ·
                refine ⟨3754363631989681304330147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502909087993120869553431 3754363631989681304330147)
                ·
                  refine ⟨5631545447984521956495221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754363631989681304330147 5631545447984521956495221)
                  ·
                    refine ⟨527957385748548933421427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5631545447984521956495221 527957385748548933421427)
                    ·
                      rfl

theorem cell23_3084580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_3084580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084580 prefixEnd_3084580 := by exact prefixLift 3084580
  have htrace : WordTrace (prefixWord ++ tailWord_3084580) baseStart_3084580 baseEnd_3084580 := by
    simpa [prefixWord, tailWord_3084580, baseEnd_3084580] using wordTrace_append hprefix tailTrace_3084580
  have hstable : (prefixWord ++ tailWord_3084580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084580).length < 2 ^ (prefixWord ++ tailWord_3084580).sum := by decide
  have hdescent : baseEnd_3084580 < baseStart_3084580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084633 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 3]
def baseStart_3084633 : Nat := 118140960795 + 3084633 * 2 ^ 59
def prefixEnd_3084633 : Nat := 4983230072969 + 3 ^ 40 * 3084633 * 2
def baseEnd_3084633 : Nat := 1583899371720335092901537

theorem tailTrace_3084633 : CollatzResearch.WordTrace tailWord_3084633 prefixEnd_3084633 1583899371720335092901537 := by
  unfold tailWord_3084633
  simp only [CollatzResearch.WordTrace]
  refine ⟨112505808233908929219754553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75003872155939286146503035 112505808233908929219754553)
  ·
    refine ⟨84379356175431696914815915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112505808233908929219754553 84379356175431696914815915)
    ·
      refine ⟨126569034263147545372223873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84379356175431696914815915 126569034263147545372223873)
      ·
        refine ⟨94926775697360659029167905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126569034263147545372223873 94926775697360659029167905)
        ·
          refine ⟨71195081773020494271875929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94926775697360659029167905 71195081773020494271875929)
          ·
            refine ⟨53396311329765370703906947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71195081773020494271875929 53396311329765370703906947)
            ·
              refine ⟨80094466994648056055860421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53396311329765370703906947 80094466994648056055860421)
              ·
                refine ⟨15017712561496510510473829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80094466994648056055860421 15017712561496510510473829)
                ·
                  refine ⟨2815821105280595720713843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15017712561496510510473829 2815821105280595720713843)
                  ·
                    refine ⟨4223731657920893581070765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2815821105280595720713843 4223731657920893581070765)
                    ·
                      refine ⟨1583899371720335092901537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4223731657920893581070765 1583899371720335092901537)
                      ·
                        rfl

theorem cell23_3084633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_3084633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084633 prefixEnd_3084633 := by exact prefixLift 3084633
  have htrace : WordTrace (prefixWord ++ tailWord_3084633) baseStart_3084633 baseEnd_3084633 := by
    simpa [prefixWord, tailWord_3084633, baseEnd_3084633] using wordTrace_append hprefix tailTrace_3084633
  have hstable : (prefixWord ++ tailWord_3084633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084633).length < 2 ^ (prefixWord ++ tailWord_3084633).sum := by decide
  have hdescent : baseEnd_3084633 < baseStart_3084633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084667 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 2, 1, 3]
def baseStart_3084667 : Nat := 118140960795 + 3084667 * 2 ^ 59
def prefixEnd_3084667 : Nat := 4983230072969 + 3 ^ 40 * 3084667 * 2
def baseEnd_3084667 : Nat := 1583916830062587959876381

theorem tailTrace_3084667 : CollatzResearch.WordTrace tailWord_3084667 prefixEnd_3084667 1583916830062587959876381 := by
  unfold tailWord_3084667
  simp only [CollatzResearch.WordTrace]
  refine ⟨112507048315785753026492255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75004698877190502017661503 112507048315785753026492255)
  ·
    refine ⟨168760572473678629539738383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112507048315785753026492255 168760572473678629539738383)
    ·
      refine ⟨253140858710517944309607575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168760572473678629539738383 253140858710517944309607575)
      ·
        refine ⟨379711288065776916464411363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253140858710517944309607575 379711288065776916464411363)
        ·
          refine ⟨569566932098665374696617045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379711288065776916464411363 569566932098665374696617045)
          ·
            refine ⟨6674612485531234859725981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 569566932098665374696617045 6674612485531234859725981)
            ·
              refine ⟨2502979682074213072397243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6674612485531234859725981 2502979682074213072397243)
              ·
                refine ⟨3754469523111319608595865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502979682074213072397243 3754469523111319608595865)
                ·
                  refine ⟨2815852142333489706446899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3754469523111319608595865 2815852142333489706446899)
                  ·
                    refine ⟨4223778213500234559670349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2815852142333489706446899 4223778213500234559670349)
                    ·
                      refine ⟨1583916830062587959876381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4223778213500234559670349 1583916830062587959876381)
                      ·
                        rfl

theorem cell23_3084667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 1, 3].length) (baseStart_3084667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084667 prefixEnd_3084667 := by exact prefixLift 3084667
  have htrace : WordTrace (prefixWord ++ tailWord_3084667) baseStart_3084667 baseEnd_3084667 := by
    simpa [prefixWord, tailWord_3084667, baseEnd_3084667] using wordTrace_append hprefix tailTrace_3084667
  have hstable : (prefixWord ++ tailWord_3084667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084667).length < 2 ^ (prefixWord ++ tailWord_3084667).sum := by decide
  have hdescent : baseEnd_3084667 < baseStart_3084667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084674 : List Nat := [3, 4, 2, 1, 3, 1, 2, 7]
def baseStart_3084674 : Nat := 118140960795 + 3084674 * 2 ^ 59
def prefixEnd_3084674 : Nat := 4983230072969 + 3 ^ 40 * 3084674 * 2
def baseEnd_3084674 : Nat := 58663719423228497499587

theorem tailTrace_3084674 : CollatzResearch.WordTrace tailWord_3084674 prefixEnd_3084674 58663719423228497499587 := by
  unfold tailWord_3084674
  simp only [CollatzResearch.WordTrace]
  refine ⟨28126825906690098305499269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75004869084506928814664717 28126825906690098305499269)
  ·
    refine ⟨5273779857504393432281113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28126825906690098305499269 5273779857504393432281113)
    ·
      refine ⟨3955334893128295074210835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5273779857504393432281113 3955334893128295074210835)
      ·
        refine ⟨5933002339692442611316253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3955334893128295074210835 5933002339692442611316253)
        ·
          refine ⟨2224875877384665979243595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5933002339692442611316253 2224875877384665979243595)
          ·
            refine ⟨3337313816076998968865393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224875877384665979243595 3337313816076998968865393)
            ·
              refine ⟨2502985362057749226649045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337313816076998968865393 2502985362057749226649045)
              ·
                refine ⟨58663719423228497499587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2502985362057749226649045 58663719423228497499587)
                ·
                  rfl

theorem cell23_3084674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 7].length) (baseStart_3084674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084674 prefixEnd_3084674 := by exact prefixLift 3084674
  have htrace : WordTrace (prefixWord ++ tailWord_3084674) baseStart_3084674 baseEnd_3084674 := by
    simpa [prefixWord, tailWord_3084674, baseEnd_3084674] using wordTrace_append hprefix tailTrace_3084674
  have hstable : (prefixWord ++ tailWord_3084674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084674).length < 2 ^ (prefixWord ++ tailWord_3084674).sum := by decide
  have hdescent : baseEnd_3084674 < baseStart_3084674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084713 : List Nat := [1, 2, 1, 1, 1, 1, 3, 8, 5]
def baseStart_3084713 : Nat := 118140960795 + 3084713 * 2 ^ 59
def prefixEnd_3084713 : Nat := 4983230072969 + 3 ^ 40 * 3084713 * 2
def baseEnd_3084713 : Nat := 175993383352521642211241

theorem tailTrace_3084713 : CollatzResearch.WordTrace tailWord_3084713 prefixEnd_3084713 175993383352521642211241 := by
  unfold tailWord_3084713
  simp only [CollatzResearch.WordTrace]
  refine ⟨112508726073619102882666793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75005817382412735255111195 112508726073619102882666793)
  ·
    refine ⟨84381544555214327162000095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112508726073619102882666793 84381544555214327162000095)
    ·
      refine ⟨126572316832821490743000143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84381544555214327162000095 126572316832821490743000143)
      ·
        refine ⟨189858475249232236114500215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126572316832821490743000143 189858475249232236114500215)
        ·
          refine ⟨284787712873848354171750323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189858475249232236114500215 284787712873848354171750323)
          ·
            refine ⟨427181569310772531257625485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284787712873848354171750323 427181569310772531257625485)
            ·
              refine ⟨160193088491539699221609557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427181569310772531257625485 160193088491539699221609557)
              ·
                refine ⟨1877262755760230850253237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 160193088491539699221609557 1877262755760230850253237)
                ·
                  refine ⟨175993383352521642211241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1877262755760230850253237 175993383352521642211241)
                  ·
                    rfl

theorem cell23_3084713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 5].length) (baseStart_3084713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084713 prefixEnd_3084713 := by exact prefixLift 3084713
  have htrace : WordTrace (prefixWord ++ tailWord_3084713) baseStart_3084713 baseEnd_3084713 := by
    simpa [prefixWord, tailWord_3084713, baseEnd_3084713] using wordTrace_append hprefix tailTrace_3084713
  have hstable : (prefixWord ++ tailWord_3084713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084713).length < 2 ^ (prefixWord ++ tailWord_3084713).sum := by decide
  have hdescent : baseEnd_3084713 < baseStart_3084713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084736 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_3084736 : Nat := 118140960795 + 3084736 * 2 ^ 59
def prefixEnd_3084736 : Nat := 4983230072969 + 3 ^ 40 * 3084736 * 2
def baseEnd_3084736 : Nat := 1583952260227748189913563

theorem tailTrace_3084736 : CollatzResearch.WordTrace tailWord_3084736 prefixEnd_3084736 1583952260227748189913563 := by
  unfold tailWord_3084736
  simp only [CollatzResearch.WordTrace]
  refine ⟨56254782476267888905377031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75006376635023851873836041 56254782476267888905377031)
  ·
    refine ⟨84382173714401833358065547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56254782476267888905377031 84382173714401833358065547)
    ·
      refine ⟨126573260571602750037098321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84382173714401833358065547 126573260571602750037098321)
      ·
        refine ⟨94929945428702062527823741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126573260571602750037098321 94929945428702062527823741)
        ·
          refine ⟨35598729535763273447933903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94929945428702062527823741 35598729535763273447933903)
          ·
            refine ⟨53398094303644910171900855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35598729535763273447933903 53398094303644910171900855)
            ·
              refine ⟨80097141455467365257851283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53398094303644910171900855 80097141455467365257851283)
              ·
                refine ⟨120145712183201047886776925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80097141455467365257851283 120145712183201047886776925)
                ·
                  refine ⟨45054642068700392957541347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120145712183201047886776925 45054642068700392957541347)
                  ·
                    refine ⟨67581963103050589436312021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45054642068700392957541347 67581963103050589436312021)
                    ·
                      refine ⟨1583952260227748189913563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67581963103050589436312021 1583952260227748189913563)
                      ·
                        rfl

theorem cell23_3084736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_3084736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084736 prefixEnd_3084736 := by exact prefixLift 3084736
  have htrace : WordTrace (prefixWord ++ tailWord_3084736) baseStart_3084736 baseEnd_3084736 := by
    simpa [prefixWord, tailWord_3084736, baseEnd_3084736] using wordTrace_append hprefix tailTrace_3084736
  have hstable : (prefixWord ++ tailWord_3084736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084736).length < 2 ^ (prefixWord ++ tailWord_3084736).sum := by decide
  have hdescent : baseEnd_3084736 < baseStart_3084736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084743 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 2, 5]
def baseStart_3084743 : Nat := 118140960795 + 3084743 * 2 ^ 59
def prefixEnd_3084743 : Nat := 4983230072969 + 3 ^ 40 * 3084743 * 2
def baseEnd_3084743 : Nat := 527985284864109887508677

theorem tailTrace_3084743 : CollatzResearch.WordTrace tailWord_3084743 prefixEnd_3084743 527985284864109887508677 := by
  unfold tailWord_3084743
  simp only [CollatzResearch.WordTrace]
  refine ⟨112509820263510418006258883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75006546842340278670839255 112509820263510418006258883)
  ·
    refine ⟨168764730395265627009388325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112509820263510418006258883 168764730395265627009388325)
    ·
      refine ⟨31643386949112305064260311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168764730395265627009388325 31643386949112305064260311)
      ·
        refine ⟨47465080423668457596390467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31643386949112305064260311 47465080423668457596390467)
        ·
          refine ⟨71197620635502686394585701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47465080423668457596390467 71197620635502686394585701)
          ·
            refine ⟨13349553869156753698984819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71197620635502686394585701 13349553869156753698984819)
            ·
              refine ⟨20024330803735130548477229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13349553869156753698984819 20024330803735130548477229)
              ·
                refine ⟨7509124051400673955678961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20024330803735130548477229 7509124051400673955678961)
                ·
                  refine ⟨5631843038550505466759221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7509124051400673955678961 5631843038550505466759221)
                  ·
                    refine ⟨527985284864109887508677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5631843038550505466759221 527985284864109887508677)
                    ·
                      rfl

theorem cell23_3084743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_3084743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084743 prefixEnd_3084743 := by exact prefixLift 3084743
  have htrace : WordTrace (prefixWord ++ tailWord_3084743) baseStart_3084743 baseEnd_3084743 := by
    simpa [prefixWord, tailWord_3084743, baseEnd_3084743] using wordTrace_append hprefix tailTrace_3084743
  have hstable : (prefixWord ++ tailWord_3084743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084743).length < 2 ^ (prefixWord ++ tailWord_3084743).sum := by decide
  have hdescent : baseEnd_3084743 < baseStart_3084743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084780 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 2, 4, 2]
def baseStart_3084780 : Nat := 118140960795 + 3084780 * 2 ^ 59
def prefixEnd_3084780 : Nat := 4983230072969 + 3 ^ 40 * 3084780 * 2
def baseEnd_3084780 : Nat := 1583974853376546017763361

theorem tailTrace_3084780 : CollatzResearch.WordTrace tailWord_3084780 prefixEnd_3084780 1583974853376546017763361 := by
  unfold tailWord_3084780
  simp only [CollatzResearch.WordTrace]
  refine ⟨56255584882188186662677897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75007446509584248883570529 56255584882188186662677897)
  ·
    refine ⟨42191688661641139997008423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56255584882188186662677897 42191688661641139997008423)
    ·
      refine ⟨63287532992461709995512635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42191688661641139997008423 63287532992461709995512635)
      ·
        refine ⟨94931299488692564993268953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63287532992461709995512635 94931299488692564993268953)
        ·
          refine ⟨71198474616519423744951715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94931299488692564993268953 71198474616519423744951715)
          ·
            refine ⟨106797711924779135617427573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71198474616519423744951715 106797711924779135617427573)
            ·
              refine ⟨10012285492948043964133835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106797711924779135617427573 10012285492948043964133835)
              ·
                refine ⟨15018428239422065946200753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10012285492948043964133835 15018428239422065946200753)
                ·
                  refine ⟨11263821179566549459650565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15018428239422065946200753 11263821179566549459650565)
                  ·
                    refine ⟨2111966471168728023684481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11263821179566549459650565 2111966471168728023684481)
                    ·
                      refine ⟨1583974853376546017763361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2111966471168728023684481 1583974853376546017763361)
                      ·
                        rfl

theorem cell23_3084780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_3084780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084780 prefixEnd_3084780 := by exact prefixLift 3084780
  have htrace : WordTrace (prefixWord ++ tailWord_3084780) baseStart_3084780 baseEnd_3084780 := by
    simpa [prefixWord, tailWord_3084780, baseEnd_3084780] using wordTrace_append hprefix tailTrace_3084780
  have hstable : (prefixWord ++ tailWord_3084780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084780).length < 2 ^ (prefixWord ++ tailWord_3084780).sum := by decide
  have hdescent : baseEnd_3084780 < baseStart_3084780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084783 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 3]
def baseStart_3084783 : Nat := 118140960795 + 3084783 * 2 ^ 59
def prefixEnd_3084783 : Nat := 4983230072969 + 3 ^ 40 * 3084783 * 2
def baseEnd_3084783 : Nat := 1583976393818509506025847

theorem tailTrace_3084783 : CollatzResearch.WordTrace tailWord_3084783 prefixEnd_3084783 1583976393818509506025847 := by
  unfold tailWord_3084783
  simp only [CollatzResearch.WordTrace]
  refine ⟨112511279183365504837715003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75007519455577003225143335 112511279183365504837715003)
  ·
    refine ⟨168766918775048257256572505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112511279183365504837715003 168766918775048257256572505)
    ·
      refine ⟨126575189081286192942429379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168766918775048257256572505 126575189081286192942429379)
      ·
        refine ⟨189862783621929289413644069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126575189081286192942429379 189862783621929289413644069)
        ·
          refine ⟨35599271929111741765058263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189862783621929289413644069 35599271929111741765058263)
          ·
            refine ⟨53398907893667612647587395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35599271929111741765058263 53398907893667612647587395)
            ·
              refine ⟨80098361840501418971381093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53398907893667612647587395 80098361840501418971381093)
              ·
                refine ⟨15018442845094016057133955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80098361840501418971381093 15018442845094016057133955)
                ·
                  refine ⟨22527664267641024085700933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15018442845094016057133955 22527664267641024085700933)
                  ·
                    refine ⟨4223937050182692016068925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22527664267641024085700933 4223937050182692016068925)
                    ·
                      refine ⟨1583976393818509506025847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4223937050182692016068925 1583976393818509506025847)
                      ·
                        rfl

theorem cell23_3084783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_3084783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084783 prefixEnd_3084783 := by exact prefixLift 3084783
  have htrace : WordTrace (prefixWord ++ tailWord_3084783) baseStart_3084783 baseEnd_3084783 := by
    simpa [prefixWord, tailWord_3084783, baseEnd_3084783] using wordTrace_append hprefix tailTrace_3084783
  have hstable : (prefixWord ++ tailWord_3084783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084783).length < 2 ^ (prefixWord ++ tailWord_3084783).sum := by decide
  have hdescent : baseEnd_3084783 < baseStart_3084783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084850 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_3084850 : Nat := 118140960795 + 3084850 * 2 ^ 59
def prefixEnd_3084850 : Nat := 4983230072969 + 3 ^ 40 * 3084850 * 2
def baseEnd_3084850 : Nat := 528003599007453581296013

theorem tailTrace_3084850 : CollatzResearch.WordTrace tailWord_3084850 prefixEnd_3084850 528003599007453581296013 := by
  unfold tailWord_3084850
  simp only [CollatzResearch.WordTrace]
  refine ⟨28128430718530693820101001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75009148582748516853602669 28128430718530693820101001)
  ·
    refine ⟨21096323038898020365075751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28128430718530693820101001 21096323038898020365075751)
    ·
      refine ⟨31644484558347030547613627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21096323038898020365075751 31644484558347030547613627)
      ·
        refine ⟨47466726837520545821420441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31644484558347030547613627 47466726837520545821420441)
        ·
          refine ⟨35600045128140409366065331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47466726837520545821420441 35600045128140409366065331)
          ·
            refine ⟨53400067692210614049097997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35600045128140409366065331 53400067692210614049097997)
            ·
              refine ⟨20025025384578980268411749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53400067692210614049097997 20025025384578980268411749)
              ·
                refine ⟨3754692259608558800327203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20025025384578980268411749 3754692259608558800327203)
                ·
                  refine ⟨5632038389412838200490805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754692259608558800327203 5632038389412838200490805)
                  ·
                    refine ⟨528003599007453581296013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5632038389412838200490805 528003599007453581296013)
                    ·
                      rfl

theorem cell23_3084850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_3084850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084850 prefixEnd_3084850 := by exact prefixLift 3084850
  have htrace : WordTrace (prefixWord ++ tailWord_3084850) baseStart_3084850 baseEnd_3084850 := by
    simpa [prefixWord, tailWord_3084850, baseEnd_3084850] using wordTrace_append hprefix tailTrace_3084850
  have hstable : (prefixWord ++ tailWord_3084850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084850).length < 2 ^ (prefixWord ++ tailWord_3084850).sum := by decide
  have hdescent : baseEnd_3084850 < baseStart_3084850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084857 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 2, 3, 2]
def baseStart_3084857 : Nat := 118140960795 + 3084857 * 2 ^ 59
def prefixEnd_3084857 : Nat := 4983230072969 + 3 ^ 40 * 3084857 * 2
def baseEnd_3084857 : Nat := 1584014391386942216500507

theorem tailTrace_3084857 : CollatzResearch.WordTrace tailWord_3084857 prefixEnd_3084857 1584014391386942216500507 := by
  unfold tailWord_3084857
  simp only [CollatzResearch.WordTrace]
  refine ⟨112513978185097415475908825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75009318790064943650605883 112513978185097415475908825)
  ·
    refine ⟨84385483638823061606931619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112513978185097415475908825 84385483638823061606931619)
    ·
      refine ⟨126578225458234592410397429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84385483638823061606931619 126578225458234592410397429)
      ·
        refine ⟨11866708636709493038474759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126578225458234592410397429 11866708636709493038474759)
        ·
          refine ⟨17800062955064239557712139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11866708636709493038474759 17800062955064239557712139)
          ·
            refine ⟨26700094432596359336568209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17800062955064239557712139 26700094432596359336568209)
            ·
              refine ⟨20025070824447269502426157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26700094432596359336568209 20025070824447269502426157)
              ·
                refine ⟨7509401559167726063409809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20025070824447269502426157 7509401559167726063409809)
                ·
                  refine ⟨5632051169375794547557357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7509401559167726063409809 5632051169375794547557357)
                  ·
                    refine ⟨2112019188515922955334009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5632051169375794547557357 2112019188515922955334009)
                    ·
                      refine ⟨1584014391386942216500507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112019188515922955334009 1584014391386942216500507)
                      ·
                        rfl

theorem cell23_3084857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_3084857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084857 prefixEnd_3084857 := by exact prefixLift 3084857
  have htrace : WordTrace (prefixWord ++ tailWord_3084857) baseStart_3084857 baseEnd_3084857 := by
    simpa [prefixWord, tailWord_3084857, baseEnd_3084857] using wordTrace_append hprefix tailTrace_3084857
  have hstable : (prefixWord ++ tailWord_3084857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084857).length < 2 ^ (prefixWord ++ tailWord_3084857).sum := by decide
  have hdescent : baseEnd_3084857 < baseStart_3084857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084863 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 3, 6]
def baseStart_3084863 : Nat := 118140960795 + 3084863 * 2 ^ 59
def prefixEnd_3084863 : Nat := 4983230072969 + 3 ^ 40 * 3084863 * 2
def baseEnd_3084863 : Nat := 528005824090289731008493

theorem tailTrace_3084863 : CollatzResearch.WordTrace tailWord_3084863 prefixEnd_3084863 528005824090289731008493 := by
  unfold tailWord_3084863
  simp only [CollatzResearch.WordTrace]
  refine ⟨112514197023075678500627243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75009464682050452333751495 112514197023075678500627243)
  ·
    refine ⟨168771295534613517750940865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112514197023075678500627243 168771295534613517750940865)
    ·
      refine ⟨126578471650960138313205649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168771295534613517750940865 126578471650960138313205649)
      ·
        refine ⟨94933853738220103734904237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126578471650960138313205649 94933853738220103734904237)
        ·
          refine ⟨35600195151832538900589089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94933853738220103734904237 35600195151832538900589089)
          ·
            refine ⟨26700146363874404175441817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35600195151832538900589089 26700146363874404175441817)
            ·
              refine ⟨20025109772905803131581363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26700146363874404175441817 20025109772905803131581363)
              ·
                refine ⟨30037664659358704697372045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20025109772905803131581363 30037664659358704697372045)
                ·
                  refine ⟨11264124247259514261514517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30037664659358704697372045 11264124247259514261514517)
                  ·
                    refine ⟨528005824090289731008493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11264124247259514261514517 528005824090289731008493)
                    ·
                      rfl

theorem cell23_3084863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_3084863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084863 prefixEnd_3084863 := by exact prefixLift 3084863
  have htrace : WordTrace (prefixWord ++ tailWord_3084863) baseStart_3084863 baseEnd_3084863 := by
    simpa [prefixWord, tailWord_3084863, baseEnd_3084863] using wordTrace_append hprefix tailTrace_3084863
  have hstable : (prefixWord ++ tailWord_3084863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084863).length < 2 ^ (prefixWord ++ tailWord_3084863).sum := by decide
  have hdescent : baseEnd_3084863 < baseStart_3084863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084864 : List Nat := [2, 1, 1, 2, 2, 2, 5, 3, 1, 1, 3]
def baseStart_3084864 : Nat := 118140960795 + 3084864 * 2 ^ 59
def prefixEnd_3084864 : Nat := 4983230072969 + 3 ^ 40 * 3084864 * 2
def baseEnd_3084864 : Nat := 1584017985751523689112975

theorem tailTrace_3084864 : CollatzResearch.WordTrace tailWord_3084864 prefixEnd_3084864 1584017985751523689112975 := by
  unfold tailWord_3084864
  simp only [CollatzResearch.WordTrace]
  refine ⟨56257116748036027835706823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75009488997381370447609097 56257116748036027835706823)
  ·
    refine ⟨84385675122054041753560235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56257116748036027835706823 84385675122054041753560235)
    ·
      refine ⟨126578512683081062630340353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84385675122054041753560235 126578512683081062630340353)
      ·
        refine ⟨94933884512310796972755265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126578512683081062630340353 94933884512310796972755265)
        ·
          refine ⟨71200413384233097729566449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94933884512310796972755265 71200413384233097729566449)
          ·
            refine ⟨53400310038174823297174837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71200413384233097729566449 53400310038174823297174837)
            ·
              refine ⟨5006279066078889684110141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53400310038174823297174837 5006279066078889684110141)
              ·
                refine ⟨1877354649779583631541303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5006279066078889684110141 1877354649779583631541303)
                ·
                  refine ⟨2816031974669375447311955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877354649779583631541303 2816031974669375447311955)
                  ·
                    refine ⟨4224047962004063170967933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2816031974669375447311955 4224047962004063170967933)
                    ·
                      refine ⟨1584017985751523689112975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4224047962004063170967933 1584017985751523689112975)
                      ·
                        rfl

theorem cell23_3084864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 1, 3].length) (baseStart_3084864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084864 prefixEnd_3084864 := by exact prefixLift 3084864
  have htrace : WordTrace (prefixWord ++ tailWord_3084864) baseStart_3084864 baseEnd_3084864 := by
    simpa [prefixWord, tailWord_3084864, baseEnd_3084864] using wordTrace_append hprefix tailTrace_3084864
  have hstable : (prefixWord ++ tailWord_3084864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084864).length < 2 ^ (prefixWord ++ tailWord_3084864).sum := by decide
  have hdescent : baseEnd_3084864 < baseStart_3084864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084881 : List Nat := [1, 2, 2, 1, 3, 4, 3, 2, 1, 1, 3]
def baseStart_3084881 : Nat := 118140960795 + 3084881 * 2 ^ 59
def prefixEnd_3084881 : Nat := 4983230072969 + 3 ^ 40 * 3084881 * 2
def baseEnd_3084881 : Nat := 1584026714922650122600397

theorem tailTrace_3084881 : CollatzResearch.WordTrace tailWord_3084881 prefixEnd_3084881 1584026714922650122600397 := by
  unfold tailWord_3084881
  simp only [CollatzResearch.WordTrace]
  refine ⟨112514853537010467574782497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75009902358006978383188331 112514853537010467574782497)
  ·
    refine ⟨84386140152757850681086873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112514853537010467574782497 84386140152757850681086873)
    ·
      refine ⟨63289605114568388010815155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84386140152757850681086873 63289605114568388010815155)
      ·
        refine ⟨94934407671852582016222733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63289605114568388010815155 94934407671852582016222733)
        ·
          refine ⟨35600402876944718256083525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94934407671852582016222733 35600402876944718256083525)
          ·
            refine ⟨6675075539427134673015661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35600402876944718256083525 6675075539427134673015661)
            ·
              refine ⟨2503153327285175502380873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6675075539427134673015661 2503153327285175502380873)
              ·
                refine ⟨1877364995463881626785655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503153327285175502380873 1877364995463881626785655)
                ·
                  refine ⟨2816047493195822440178483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877364995463881626785655 2816047493195822440178483)
                  ·
                    refine ⟨4224071239793733660267725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2816047493195822440178483 4224071239793733660267725)
                    ·
                      refine ⟨1584026714922650122600397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4224071239793733660267725 1584026714922650122600397)
                      ·
                        rfl

theorem cell23_3084881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 1, 3].length) (baseStart_3084881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084881 prefixEnd_3084881 := by exact prefixLift 3084881
  have htrace : WordTrace (prefixWord ++ tailWord_3084881) baseStart_3084881 baseEnd_3084881 := by
    simpa [prefixWord, tailWord_3084881, baseEnd_3084881] using wordTrace_append hprefix tailTrace_3084881
  have hstable : (prefixWord ++ tailWord_3084881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084881).length < 2 ^ (prefixWord ++ tailWord_3084881).sum := by decide
  have hdescent : baseEnd_3084881 < baseStart_3084881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084897 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 2, 4]
def baseStart_3084897 : Nat := 118140960795 + 3084897 * 2 ^ 59
def prefixEnd_3084897 : Nat := 4983230072969 + 3 ^ 40 * 3084897 * 2
def baseEnd_3084897 : Nat := 528011643537707353333441

theorem tailTrace_3084897 : CollatzResearch.WordTrace tailWord_3084897 prefixEnd_3084897 528011643537707353333441 := by
  unfold tailWord_3084897
  simp only [CollatzResearch.WordTrace]
  refine ⟨112515437104952502307364945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75010291403301668204909963 112515437104952502307364945)
  ·
    refine ⟨84386577828714376730523709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112515437104952502307364945 84386577828714376730523709)
    ·
      refine ⟨31644966685767891273946391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84386577828714376730523709 31644966685767891273946391)
      ·
        refine ⟨47467450028651836910919587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31644966685767891273946391 47467450028651836910919587)
        ·
          refine ⟨71201175042977755366379381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47467450028651836910919587 71201175042977755366379381)
          ·
            refine ⟨6675110160279164565598067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71201175042977755366379381 6675110160279164565598067)
            ·
              refine ⟨10012665240418746848397101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6675110160279164565598067 10012665240418746848397101)
              ·
                refine ⟨3754749465157030068148913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10012665240418746848397101 3754749465157030068148913)
                ·
                  refine ⟨2816062098867772551111685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3754749465157030068148913 2816062098867772551111685)
                  ·
                    refine ⟨528011643537707353333441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2816062098867772551111685 528011643537707353333441)
                    ·
                      rfl

theorem cell23_3084897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_3084897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084897 prefixEnd_3084897 := by exact prefixLift 3084897
  have htrace : WordTrace (prefixWord ++ tailWord_3084897) baseStart_3084897 baseEnd_3084897 := by
    simpa [prefixWord, tailWord_3084897, baseEnd_3084897] using wordTrace_append hprefix tailTrace_3084897
  have hstable : (prefixWord ++ tailWord_3084897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084897).length < 2 ^ (prefixWord ++ tailWord_3084897).sum := by decide
  have hdescent : baseEnd_3084897 < baseStart_3084897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084900 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_3084900 : Nat := 118140960795 + 3084900 * 2 ^ 59
def prefixEnd_3084900 : Nat := 4983230072969 + 3 ^ 40 * 3084900 * 2
def baseEnd_3084900 : Nat := 1584036471055085548262809

theorem tailTrace_3084900 : CollatzResearch.WordTrace tailWord_3084900 prefixEnd_3084900 1584036471055085548262809 := by
  unfold tailWord_3084900
  simp only [CollatzResearch.WordTrace]
  refine ⟨56257773261970816909862077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75010364349294422546482769 56257773261970816909862077)
  ·
    refine ⟨21096664973239056341198279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56257773261970816909862077 21096664973239056341198279)
    ·
      refine ⟨31644997459858584511797419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21096664973239056341198279 31644997459858584511797419)
      ·
        refine ⟨47467496189787876767696129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31644997459858584511797419 47467496189787876767696129)
        ·
          refine ⟨35600622142340907575772097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47467496189787876767696129 35600622142340907575772097)
          ·
            refine ⟨26700466606755680681829073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35600622142340907575772097 26700466606755680681829073)
            ·
              refine ⟨20025349955066760511371805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26700466606755680681829073 20025349955066760511371805)
              ·
                refine ⟨7509506233150035191764427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20025349955066760511371805 7509506233150035191764427)
                ·
                  refine ⟨11264259349725052787646641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7509506233150035191764427 11264259349725052787646641)
                  ·
                    refine ⟨8448194512293789590734981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11264259349725052787646641 8448194512293789590734981)
                    ·
                      refine ⟨1584036471055085548262809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8448194512293789590734981 1584036471055085548262809)
                      ·
                        rfl

theorem cell23_3084900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_3084900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084900 prefixEnd_3084900 := by exact prefixLift 3084900
  have htrace : WordTrace (prefixWord ++ tailWord_3084900) baseStart_3084900 baseEnd_3084900 := by
    simpa [prefixWord, tailWord_3084900, baseEnd_3084900] using wordTrace_append hprefix tailTrace_3084900
  have hstable : (prefixWord ++ tailWord_3084900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084900).length < 2 ^ (prefixWord ++ tailWord_3084900).sum := by decide
  have hdescent : baseEnd_3084900 < baseStart_3084900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084910 : List Nat := [4, 1, 2, 2, 2, 1, 2, 9]
def baseStart_3084910 : Nat := 118140960795 + 3084910 * 2 ^ 59
def prefixEnd_3084910 : Nat := 4983230072969 + 3 ^ 40 * 3084910 * 2
def baseEnd_3084910 : Nat := 58668207624504833671769

theorem tailTrace_3084910 : CollatzResearch.WordTrace tailWord_3084910 prefixEnd_3084910 58668207624504833671769 := by
  unfold tailWord_3084910
  simp only [CollatzResearch.WordTrace]
  refine ⟨14064488906738175690948523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75010607502603603685058789 14064488906738175690948523)
  ·
    refine ⟨21096733360107263536422785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14064488906738175690948523 21096733360107263536422785)
    ·
      refine ⟨15822550020080447652317089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21096733360107263536422785 15822550020080447652317089)
      ·
        refine ⟨11866912515060335739237817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15822550020080447652317089 11866912515060335739237817)
        ·
          refine ⟨8900184386295251804428363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11866912515060335739237817 8900184386295251804428363)
          ·
            refine ⟨13350276579442877706642545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900184386295251804428363 13350276579442877706642545)
            ·
              refine ⟨10012707434582158279981909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13350276579442877706642545 10012707434582158279981909)
              ·
                refine ⟨58668207624504833671769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10012707434582158279981909 58668207624504833671769)
                ·
                  rfl

theorem cell23_3084910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_3084910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084910 prefixEnd_3084910 := by exact prefixLift 3084910
  have htrace : WordTrace (prefixWord ++ tailWord_3084910) baseStart_3084910 baseEnd_3084910 := by
    simpa [prefixWord, tailWord_3084910, baseEnd_3084910] using wordTrace_append hprefix tailTrace_3084910
  have hstable : (prefixWord ++ tailWord_3084910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084910).length < 2 ^ (prefixWord ++ tailWord_3084910).sum := by decide
  have hdescent : baseEnd_3084910 < baseStart_3084910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084920 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_3084920 : Nat := 118140960795 + 3084920 * 2 ^ 59
def prefixEnd_3084920 : Nat := 4983230072969 + 3 ^ 40 * 3084920 * 2
def baseEnd_3084920 : Nat := 1584046740668175470012717

theorem tailTrace_3084920 : CollatzResearch.WordTrace tailWord_3084920 prefixEnd_3084920 1584046740668175470012717 := by
  unfold tailWord_3084920
  simp only [CollatzResearch.WordTrace]
  refine ⟨56258137991934588617726107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75010850655912784823634809 56258137991934588617726107)
  ·
    refine ⟨84387206987901882926589161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56258137991934588617726107 84387206987901882926589161)
    ·
      refine ⟨63290405240926412194941871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84387206987901882926589161 63290405240926412194941871)
      ·
        refine ⟨94935607861389618292412807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63290405240926412194941871 94935607861389618292412807)
        ·
          refine ⟨142403411792084427438619211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94935607861389618292412807 142403411792084427438619211)
          ·
            refine ⟨213605117688126641157928817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142403411792084427438619211 213605117688126641157928817)
            ·
              refine ⟨160203838266094980868446613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213605117688126641157928817 160203838266094980868446613)
              ·
                refine ⟨7509554918723202228208435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160203838266094980868446613 7509554918723202228208435)
                ·
                  refine ⟨11264332378084803342312653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7509554918723202228208435 11264332378084803342312653)
                  ·
                    refine ⟨4224124641781801253367245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11264332378084803342312653 4224124641781801253367245)
                    ·
                      refine ⟨1584046740668175470012717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4224124641781801253367245 1584046740668175470012717)
                      ·
                        rfl

theorem cell23_3084920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_3084920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084920 prefixEnd_3084920 := by exact prefixLift 3084920
  have htrace : WordTrace (prefixWord ++ tailWord_3084920) baseStart_3084920 baseEnd_3084920 := by
    simpa [prefixWord, tailWord_3084920, baseEnd_3084920] using wordTrace_append hprefix tailTrace_3084920
  have hstable : (prefixWord ++ tailWord_3084920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084920).length < 2 ^ (prefixWord ++ tailWord_3084920).sum := by decide
  have hdescent : baseEnd_3084920 < baseStart_3084920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084938 : List Nat := [3, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2]
def baseStart_3084938 : Nat := 118140960795 + 3084938 * 2 ^ 59
def prefixEnd_3084938 : Nat := 4983230072969 + 3 ^ 40 * 3084938 * 2
def baseEnd_3084938 : Nat := 1584055983319956399587635

theorem tailTrace_3084938 : CollatzResearch.WordTrace tailWord_3084938 prefixEnd_3084938 1584055983319956399587635 := by
  unfold tailWord_3084938
  simp only [CollatzResearch.WordTrace]
  refine ⟨28129233124450991577401867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75011288331869310873071645 28129233124450991577401867)
  ·
    refine ⟨42193849686676487366102801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28129233124450991577401867 42193849686676487366102801)
    ·
      refine ⟨31645387265007365524577101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42193849686676487366102801 31645387265007365524577101)
      ·
        refine ⟨11867020224377762071716413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31645387265007365524577101 11867020224377762071716413)
        ·
          refine ⟨4450132584141660776893655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11867020224377762071716413 4450132584141660776893655)
          ·
            refine ⟨6675198876212491165340483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4450132584141660776893655 6675198876212491165340483)
            ·
              refine ⟨10012798314318736748010725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6675198876212491165340483 10012798314318736748010725)
              ·
                refine ⟨1877399683934763140252011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10012798314318736748010725 1877399683934763140252011)
                ·
                  refine ⟨2816099525902144710378017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877399683934763140252011 2816099525902144710378017)
                  ·
                    refine ⟨2112074644426608532783513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2816099525902144710378017 2112074644426608532783513)
                    ·
                      refine ⟨1584055983319956399587635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112074644426608532783513 1584055983319956399587635)
                      ·
                        rfl

theorem cell23_3084938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_3084938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084938 prefixEnd_3084938 := by exact prefixLift 3084938
  have htrace : WordTrace (prefixWord ++ tailWord_3084938) baseStart_3084938 baseEnd_3084938 := by
    simpa [prefixWord, tailWord_3084938, baseEnd_3084938] using wordTrace_append hprefix tailTrace_3084938
  have hstable : (prefixWord ++ tailWord_3084938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084938).length < 2 ^ (prefixWord ++ tailWord_3084938).sum := by decide
  have hdescent : baseEnd_3084938 < baseStart_3084938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084964 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_3084964 : Nat := 118140960795 + 3084964 * 2 ^ 59
def prefixEnd_3084964 : Nat := 4983230072969 + 3 ^ 40 * 3084964 * 2
def baseEnd_3084964 : Nat := 1584069333816973297862515

theorem tailTrace_3084964 : CollatzResearch.WordTrace tailWord_3084964 prefixEnd_3084964 1584069333816973297862515 := by
  unfold tailWord_3084964
  simp only [CollatzResearch.WordTrace]
  refine ⟨56258940397854886375026973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75011920530473181833369297 56258940397854886375026973)
  ·
    refine ⟨21097102649195582390635115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56258940397854886375026973 21097102649195582390635115)
    ·
      refine ⟨31645653973793373585952673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21097102649195582390635115 31645653973793373585952673)
      ·
        refine ⟨23734240480345030189464505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31645653973793373585952673 23734240480345030189464505)
        ·
          refine ⟨17800680360258772642098379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23734240480345030189464505 17800680360258772642098379)
          ·
            refine ⟨26701020540388158963147569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17800680360258772642098379 26701020540388158963147569)
            ·
              refine ⟨20025765405291119222360677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26701020540388158963147569 20025765405291119222360677)
              ·
                refine ⟨3754831013492084854192627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20025765405291119222360677 3754831013492084854192627)
                ·
                  refine ⟨5632246520238127281288941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754831013492084854192627 5632246520238127281288941)
                  ·
                    refine ⟨2112092445089297730483353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5632246520238127281288941 2112092445089297730483353)
                    ·
                      refine ⟨1584069333816973297862515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112092445089297730483353 1584069333816973297862515)
                      ·
                        rfl

theorem cell23_3084964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_3084964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084964 prefixEnd_3084964 := by exact prefixLift 3084964
  have htrace : WordTrace (prefixWord ++ tailWord_3084964) baseStart_3084964 baseEnd_3084964 := by
    simpa [prefixWord, tailWord_3084964, baseEnd_3084964] using wordTrace_append hprefix tailTrace_3084964
  have hstable : (prefixWord ++ tailWord_3084964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084964).length < 2 ^ (prefixWord ++ tailWord_3084964).sum := by decide
  have hdescent : baseEnd_3084964 < baseStart_3084964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3084981 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_3084981 : Nat := 118140960795 + 3084981 * 2 ^ 59
def prefixEnd_3084981 : Nat := 4983230072969 + 3 ^ 40 * 3084981 * 2
def baseEnd_3084981 : Nat := 1584078062988099731349937

theorem tailTrace_3084981 : CollatzResearch.WordTrace tailWord_3084981 prefixEnd_3084981 1584078062988099731349937 := by
  unfold tailWord_3084981
  simp only [CollatzResearch.WordTrace]
  refine ⟨112518500836648184653422797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75012333891098789768948531 112518500836648184653422797)
  ·
    refine ⟨42194437813743069245033549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112518500836648184653422797 42194437813743069245033549)
    ·
      refine ⟨15822914180153650966887581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42194437813743069245033549 15822914180153650966887581)
      ·
        refine ⟨5933592817557619112582843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15822914180153650966887581 5933592817557619112582843)
        ·
          refine ⟨8900389226336428668874265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5933592817557619112582843 8900389226336428668874265)
          ·
            refine ⟨6675291919752321501655699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8900389226336428668874265 6675291919752321501655699)
            ·
              refine ⟨10012937879628482252483549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6675291919752321501655699 10012937879628482252483549)
              ·
                refine ⟨3754851704860680844681331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10012937879628482252483549 3754851704860680844681331)
                ·
                  refine ⟨5632277557291021267021997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754851704860680844681331 5632277557291021267021997)
                  ·
                    refine ⟨2112104083984132975133249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5632277557291021267021997 2112104083984132975133249)
                    ·
                      refine ⟨1584078062988099731349937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112104083984132975133249 1584078062988099731349937)
                      ·
                        rfl

theorem cell23_3084981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_3084981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3084981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3084981 prefixEnd_3084981 := by exact prefixLift 3084981
  have htrace : WordTrace (prefixWord ++ tailWord_3084981) baseStart_3084981 baseEnd_3084981 := by
    simpa [prefixWord, tailWord_3084981, baseEnd_3084981] using wordTrace_append hprefix tailTrace_3084981
  have hstable : (prefixWord ++ tailWord_3084981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3084981).length < 2 ^ (prefixWord ++ tailWord_3084981).sum := by decide
  have hdescent : baseEnd_3084981 < baseStart_3084981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3084981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085000 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 7]
def baseStart_3085000 : Nat := 118140960795 + 3085000 * 2 ^ 59
def prefixEnd_3085000 : Nat := 4983230072969 + 3 ^ 40 * 3085000 * 2
def baseEnd_3085000 : Nat := 176009757680059461890261

theorem tailTrace_3085000 : CollatzResearch.WordTrace tailWord_3085000 prefixEnd_3085000 176009757680059461890261 := by
  unfold tailWord_3085000
  simp only [CollatzResearch.WordTrace]
  refine ⟨56259596911789675449182227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75012795882386233932242969 56259596911789675449182227)
  ·
    refine ⟨84389395367684513173773341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56259596911789675449182227 84389395367684513173773341)
    ·
      refine ⟨31646023262881692440165003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84389395367684513173773341 31646023262881692440165003)
      ·
        refine ⟨47469034894322538660247505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31646023262881692440165003 47469034894322538660247505)
        ·
          refine ⟨35601776170741903995185629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47469034894322538660247505 35601776170741903995185629)
          ·
            refine ⟨13350666064028213998194611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35601776170741903995185629 13350666064028213998194611)
            ·
              refine ⟨20025999096042320997291917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13350666064028213998194611 20025999096042320997291917)
              ·
                refine ⟨7509749661015870373984469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20025999096042320997291917 7509749661015870373984469)
                ·
                  refine ⟨176009757680059461890261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7509749661015870373984469 176009757680059461890261)
                  ·
                    rfl

theorem cell23_3085000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 7].length) (baseStart_3085000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085000 prefixEnd_3085000 := by exact prefixLift 3085000
  have htrace : WordTrace (prefixWord ++ tailWord_3085000) baseStart_3085000 baseEnd_3085000 := by
    simpa [prefixWord, tailWord_3085000, baseEnd_3085000] using wordTrace_append hprefix tailTrace_3085000
  have hstable : (prefixWord ++ tailWord_3085000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085000).length < 2 ^ (prefixWord ++ tailWord_3085000).sum := by decide
  have hdescent : baseEnd_3085000 < baseStart_3085000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085005 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_3085005 : Nat := 118140960795 + 3085005 * 2 ^ 59
def prefixEnd_3085005 : Nat := 4983230072969 + 3 ^ 40 * 3085005 * 2
def baseEnd_3085005 : Nat := 1584090386523807637449827

theorem tailTrace_3085005 : CollatzResearch.WordTrace tailWord_3085005 prefixEnd_3085005 1584090386523807637449827 := by
  unfold tailWord_3085005
  simp only [CollatzResearch.WordTrace]
  refine ⟨112519376188561236752296469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75012917459040824501530979 112519376188561236752296469)
  ·
    refine ⟨5274345758838807972763897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112519376188561236752296469 5274345758838807972763897)
    ·
      refine ⟨3955759319129105979572923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5274345758838807972763897 3955759319129105979572923)
      ·
        refine ⟨5933638978693658969359385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3955759319129105979572923 5933638978693658969359385)
        ·
          refine ⟨4450229234020244227019539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5933638978693658969359385 4450229234020244227019539)
          ·
            refine ⟨6675343851030366340529309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4450229234020244227019539 6675343851030366340529309)
            ·
              refine ⟨2503253944136387377698491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6675343851030366340529309 2503253944136387377698491)
              ·
                refine ⟨3754880916204581066547737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503253944136387377698491 3754880916204581066547737)
                ·
                  refine ⟨2816160687153435799910803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3754880916204581066547737 2816160687153435799910803)
                  ·
                    refine ⟨4224241030730153699866205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2816160687153435799910803 4224241030730153699866205)
                    ·
                      refine ⟨1584090386523807637449827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4224241030730153699866205 1584090386523807637449827)
                      ·
                        rfl

theorem cell23_3085005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_3085005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085005 prefixEnd_3085005 := by exact prefixLift 3085005
  have htrace : WordTrace (prefixWord ++ tailWord_3085005) baseStart_3085005 baseEnd_3085005 := by
    simpa [prefixWord, tailWord_3085005, baseEnd_3085005] using wordTrace_append hprefix tailTrace_3085005
  have hstable : (prefixWord ++ tailWord_3085005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085005).length < 2 ^ (prefixWord ++ tailWord_3085005).sum := by decide
  have hdescent : baseEnd_3085005 < baseStart_3085005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085040 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_3085040 : Nat := 118140960795 + 3085040 * 2 ^ 59
def prefixEnd_3085040 : Nat := 4983230072969 + 3 ^ 40 * 3085040 * 2
def baseEnd_3085040 : Nat := 1584108358346715000512165

theorem tailTrace_3085040 : CollatzResearch.WordTrace tailWord_3085040 prefixEnd_3085040 1584108358346715000512165 := by
  unfold tailWord_3085040
  simp only [CollatzResearch.WordTrace]
  refine ⟨56260326371717218864910287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75013768495622958486547049 56260326371717218864910287)
  ·
    refine ⟨84390489557575828297365431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56260326371717218864910287 84390489557575828297365431)
    ·
      refine ⟨126585734336363742446048147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84390489557575828297365431 126585734336363742446048147)
      ·
        refine ⟨189878601504545613669072221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126585734336363742446048147 189878601504545613669072221)
        ·
          refine ⟨71204475564204605125902083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189878601504545613669072221 71204475564204605125902083)
          ·
            refine ⟨106806713346306907688853125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71204475564204605125902083 106806713346306907688853125)
            ·
              refine ⟨20026258752432545191659961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106806713346306907688853125 20026258752432545191659961)
              ·
                refine ⟨15019694064324408893744971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20026258752432545191659961 15019694064324408893744971)
                ·
                  refine ⟨22529541096486613340617457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15019694064324408893744971 22529541096486613340617457)
                  ·
                    refine ⟨16897155822364960005463093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22529541096486613340617457 16897155822364960005463093)
                    ·
                      refine ⟨1584108358346715000512165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16897155822364960005463093 1584108358346715000512165)
                      ·
                        rfl

theorem cell23_3085040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_3085040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085040 prefixEnd_3085040 := by exact prefixLift 3085040
  have htrace : WordTrace (prefixWord ++ tailWord_3085040) baseStart_3085040 baseEnd_3085040 := by
    simpa [prefixWord, tailWord_3085040, baseEnd_3085040] using wordTrace_append hprefix tailTrace_3085040
  have hstable : (prefixWord ++ tailWord_3085040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085040).length < 2 ^ (prefixWord ++ tailWord_3085040).sum := by decide
  have hdescent : baseEnd_3085040 < baseStart_3085040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085067 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 1, 6, 2]
def baseStart_3085067 : Nat := 118140960795 + 3085067 * 2 ^ 59
def prefixEnd_3085067 : Nat := 4983230072969 + 3 ^ 40 * 3085067 * 2
def baseEnd_3085067 : Nat := 1584122222324386394874541

theorem tailTrace_3085067 : CollatzResearch.WordTrace tailWord_3085067 prefixEnd_3085067 1584122222324386394874541 := by
  unfold tailWord_3085067
  simp only [CollatzResearch.WordTrace]
  refine ⟨112521637514336621341053455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75014425009557747560702303 112521637514336621341053455)
  ·
    refine ⟨168782456271504932011580183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112521637514336621341053455 168782456271504932011580183)
    ·
      refine ⟨253173684407257398017370275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168782456271504932011580183 253173684407257398017370275)
      ·
        refine ⟨379760526610886097026055413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253173684407257398017370275 379760526610886097026055413)
        ·
          refine ⟨35602549369770571596192695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 379760526610886097026055413 35602549369770571596192695)
          ·
            refine ⟨53403824054655857394289043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35602549369770571596192695 53403824054655857394289043)
            ·
              refine ⟨80105736081983786091433565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53403824054655857394289043 80105736081983786091433565)
              ·
                refine ⟨30039651030743919784287587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80105736081983786091433565 30039651030743919784287587)
                ·
                  refine ⟨45059476546115879676431381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30039651030743919784287587 45059476546115879676431381)
                  ·
                    refine ⟨2112162963099181859832721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45059476546115879676431381 2112162963099181859832721)
                    ·
                      refine ⟨1584122222324386394874541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112162963099181859832721 1584122222324386394874541)
                      ·
                        rfl

theorem cell23_3085067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 6, 2].length) (baseStart_3085067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085067 prefixEnd_3085067 := by exact prefixLift 3085067
  have htrace : WordTrace (prefixWord ++ tailWord_3085067) baseStart_3085067 baseEnd_3085067 := by
    simpa [prefixWord, tailWord_3085067, baseEnd_3085067] using wordTrace_append hprefix tailTrace_3085067
  have hstable : (prefixWord ++ tailWord_3085067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085067).length < 2 ^ (prefixWord ++ tailWord_3085067).sum := by decide
  have hdescent : baseEnd_3085067 < baseStart_3085067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085077 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_3085077 : Nat := 118140960795 + 3085077 * 2 ^ 59
def prefixEnd_3085077 : Nat := 4983230072969 + 3 ^ 40 * 3085077 * 2
def baseEnd_3085077 : Nat := 528042452376977118583165

theorem tailTrace_3085077 : CollatzResearch.WordTrace tailWord_3085077 prefixEnd_3085077 528042452376977118583165 := by
  unfold tailWord_3085077
  simp only [CollatzResearch.WordTrace]
  refine ⟨112522002244300393048917485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75014668162866928699278323 112522002244300393048917485)
  ·
    refine ⟨42195750841612647393344057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112522002244300393048917485 42195750841612647393344057)
    ·
      refine ⟨31646813131209485545008043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42195750841612647393344057 31646813131209485545008043)
      ·
        refine ⟨47470219696814228317512065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31646813131209485545008043 47470219696814228317512065)
        ·
          refine ⟨35602664772610671238134049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47470219696814228317512065 35602664772610671238134049)
          ·
            refine ⟨26701998579458003428600537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35602664772610671238134049 26701998579458003428600537)
            ·
              refine ⟨20026498934593502571450403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26701998579458003428600537 20026498934593502571450403)
              ·
                refine ⟨30039748401890253857175605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20026498934593502571450403 30039748401890253857175605)
                ·
                  refine ⟨2816226412677211299110213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30039748401890253857175605 2816226412677211299110213)
                  ·
                    refine ⟨528042452376977118583165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2816226412677211299110213 528042452376977118583165)
                    ·
                      rfl

theorem cell23_3085077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_3085077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085077 prefixEnd_3085077 := by exact prefixLift 3085077
  have htrace : WordTrace (prefixWord ++ tailWord_3085077) baseStart_3085077 baseEnd_3085077 := by
    simpa [prefixWord, tailWord_3085077, baseEnd_3085077] using wordTrace_append hprefix tailTrace_3085077
  have hstable : (prefixWord ++ tailWord_3085077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085077).length < 2 ^ (prefixWord ++ tailWord_3085077).sum := by decide
  have hdescent : baseEnd_3085077 < baseStart_3085077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085080 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3085080 : Nat := 118140960795 + 3085080 * 2 ^ 59
def prefixEnd_3085080 : Nat := 4983230072969 + 3 ^ 40 * 3085080 * 2
def baseEnd_3085080 : Nat := 1584128897572894844011981

theorem tailTrace_3085080 : CollatzResearch.WordTrace tailWord_3085080 prefixEnd_3085080 1584128897572894844011981 := by
  unfold tailWord_3085080
  simp only [CollatzResearch.WordTrace]
  refine ⟨56261055831644762280638347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75014741108859683040851129 56261055831644762280638347)
  ·
    refine ⟨84391583747467143420957521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56261055831644762280638347 84391583747467143420957521)
    ·
      refine ⟨63293687810600357565718141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84391583747467143420957521 63293687810600357565718141)
      ·
        refine ⟨23735132928975134087144303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63293687810600357565718141 23735132928975134087144303)
        ·
          refine ⟨35602699393462701130716455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23735132928975134087144303 35602699393462701130716455)
          ·
            refine ⟨53404049090194051696074683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35602699393462701130716455 53404049090194051696074683)
            ·
              refine ⟨80106073635291077544112025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53404049090194051696074683 80106073635291077544112025)
              ·
                refine ⟨60079555226468308158084019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80106073635291077544112025 60079555226468308158084019)
                ·
                  refine ⟨90119332839702462237126029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60079555226468308158084019 90119332839702462237126029)
                  ·
                    refine ⟨33794749814888423338922261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90119332839702462237126029 33794749814888423338922261)
                    ·
                      refine ⟨1584128897572894844011981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33794749814888423338922261 1584128897572894844011981)
                      ·
                        rfl

theorem cell23_3085080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3085080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085080 prefixEnd_3085080 := by exact prefixLift 3085080
  have htrace : WordTrace (prefixWord ++ tailWord_3085080) baseStart_3085080 baseEnd_3085080 := by
    simpa [prefixWord, tailWord_3085080, baseEnd_3085080] using wordTrace_append hprefix tailTrace_3085080
  have hstable : (prefixWord ++ tailWord_3085080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085080).length < 2 ^ (prefixWord ++ tailWord_3085080).sum := by decide
  have hdescent : baseEnd_3085080 < baseStart_3085080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085084 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_3085084 : Nat := 118140960795 + 3085084 * 2 ^ 59
def prefixEnd_3085084 : Nat := 4983230072969 + 3 ^ 40 * 3085084 * 2
def baseEnd_3085084 : Nat := 1584130951495512828361963

theorem tailTrace_3085084 : CollatzResearch.WordTrace tailWord_3085084 prefixEnd_3085084 1584130951495512828361963 := by
  unfold tailWord_3085084
  simp only [CollatzResearch.WordTrace]
  refine ⟨56261128777637516622211153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75014838370183355496281537 56261128777637516622211153)
  ·
    refine ⟨42195846583228137466658365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56261128777637516622211153 42195846583228137466658365)
    ·
      refine ⟨15823442468710551549996887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42195846583228137466658365 15823442468710551549996887)
      ·
        refine ⟨23735163703065827324995331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15823442468710551549996887 23735163703065827324995331)
        ·
          refine ⟨35602745554598740987492997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23735163703065827324995331 35602745554598740987492997)
          ·
            refine ⟨6675514791487263935154937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35602745554598740987492997 6675514791487263935154937)
            ·
              refine ⟨5006636093615447951366203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6675514791487263935154937 5006636093615447951366203)
              ·
                refine ⟨7509954140423171927049305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5006636093615447951366203 7509954140423171927049305)
                ·
                  refine ⟨5632465605317378945286979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7509954140423171927049305 5632465605317378945286979)
                  ·
                    refine ⟨8448698407976068417930469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5632465605317378945286979 8448698407976068417930469)
                    ·
                      refine ⟨1584130951495512828361963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8448698407976068417930469 1584130951495512828361963)
                      ·
                        rfl

theorem cell23_3085084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_3085084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085084 prefixEnd_3085084 := by exact prefixLift 3085084
  have htrace : WordTrace (prefixWord ++ tailWord_3085084) baseStart_3085084 baseEnd_3085084 := by
    simpa [prefixWord, tailWord_3085084, baseEnd_3085084] using wordTrace_append hprefix tailTrace_3085084
  have hstable : (prefixWord ++ tailWord_3085084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085084).length < 2 ^ (prefixWord ++ tailWord_3085084).sum := by decide
  have hdescent : baseEnd_3085084 < baseStart_3085084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085107 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 6]
def baseStart_3085107 : Nat := 118140960795 + 3085107 * 2 ^ 59
def prefixEnd_3085107 : Nat := 4983230072969 + 3 ^ 40 * 3085107 * 2
def baseEnd_3085107 : Nat := 176015862394507359819373

theorem tailTrace_3085107 : CollatzResearch.WordTrace tailWord_3085107 prefixEnd_3085107 176015862394507359819373 := by
  unfold tailWord_3085107
  simp only [CollatzResearch.WordTrace]
  refine ⟨112523096434191708172509575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75015397622794472115006383 112523096434191708172509575)
  ·
    refine ⟨168784644651287562258764363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112523096434191708172509575 168784644651287562258764363)
    ·
      refine ⟨253176966976931343388146545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168784644651287562258764363 253176966976931343388146545)
      ·
        refine ⟨189882725232698507541109909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253176966976931343388146545 189882725232698507541109909)
        ·
          refine ⟨8900752745282742540989527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 189882725232698507541109909 8900752745282742540989527)
          ·
            refine ⟨13351129117924113811484291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900752745282742540989527 13351129117924113811484291)
            ·
              refine ⟨20026693676886170717226437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13351129117924113811484291 20026693676886170717226437)
              ·
                refine ⟨3755005064416157009479957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20026693676886170717226437 3755005064416157009479957)
                ·
                  refine ⟨176015862394507359819373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3755005064416157009479957 176015862394507359819373)
                  ·
                    rfl

theorem cell23_3085107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 6].length) (baseStart_3085107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085107 prefixEnd_3085107 := by exact prefixLift 3085107
  have htrace : WordTrace (prefixWord ++ tailWord_3085107) baseStart_3085107 baseEnd_3085107 := by
    simpa [prefixWord, tailWord_3085107, baseEnd_3085107] using wordTrace_append hprefix tailTrace_3085107
  have hstable : (prefixWord ++ tailWord_3085107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085107).length < 2 ^ (prefixWord ++ tailWord_3085107).sum := by decide
  have hdescent : baseEnd_3085107 < baseStart_3085107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085177 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3085177 : Nat := 118140960795 + 3085177 * 2 ^ 59
def prefixEnd_3085177 : Nat := 4983230072969 + 3 ^ 40 * 3085177 * 2
def baseEnd_3085177 : Nat := 1584178705196380964499035

theorem tailTrace_3085177 : CollatzResearch.WordTrace tailWord_3085177 prefixEnd_3085177 1584178705196380964499035 := by
  unfold tailWord_3085177
  simp only [CollatzResearch.WordTrace]
  refine ⟨112525649543938110127557785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75017099695958740085038523 112525649543938110127557785)
  ·
    refine ⟨84394237157953582595668339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112525649543938110127557785 84394237157953582595668339)
    ·
      refine ⟨126591355736930373893502509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84394237157953582595668339 126591355736930373893502509)
      ·
        refine ⟨47471758401348890210063441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126591355736930373893502509 47471758401348890210063441)
        ·
          refine ⟨35603818801011667657547581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47471758401348890210063441 35603818801011667657547581)
          ·
            refine ⟨13351432050379375371580343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35603818801011667657547581 13351432050379375371580343)
            ·
              refine ⟨20027148075569063057370515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13351432050379375371580343 20027148075569063057370515)
              ·
                refine ⟨30040722113353594586055773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20027148075569063057370515 30040722113353594586055773)
                ·
                  refine ⟨11265270792507597969770915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30040722113353594586055773 11265270792507597969770915)
                  ·
                    refine ⟨16897906188761396954656373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11265270792507597969770915 16897906188761396954656373)
                    ·
                      refine ⟨1584178705196380964499035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16897906188761396954656373 1584178705196380964499035)
                      ·
                        rfl

theorem cell23_3085177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3085177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085177 prefixEnd_3085177 := by exact prefixLift 3085177
  have htrace : WordTrace (prefixWord ++ tailWord_3085177) baseStart_3085177 baseEnd_3085177 := by
    simpa [prefixWord, tailWord_3085177, baseEnd_3085177] using wordTrace_append hprefix tailTrace_3085177
  have hstable : (prefixWord ++ tailWord_3085177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085177).length < 2 ^ (prefixWord ++ tailWord_3085177).sum := by decide
  have hdescent : baseEnd_3085177 < baseStart_3085177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085187 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 6]
def baseStart_3085187 : Nat := 118140960795 + 3085187 * 2 ^ 59
def prefixEnd_3085187 : Nat := 4983230072969 + 3 ^ 40 * 3085187 * 2
def baseEnd_3085187 : Nat := 1584183840002925925373989

theorem tailTrace_3085187 : CollatzResearch.WordTrace tailWord_3085187 prefixEnd_3085187 1584183840002925925373989 := by
  unfold tailWord_3085187
  simp only [CollatzResearch.WordTrace]
  refine ⟨112526014273901881835421815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75017342849267921223614543 112526014273901881835421815)
  ·
    refine ⟨168789021410852822753132723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112526014273901881835421815 168789021410852822753132723)
    ·
      refine ⟨253183532116279234129699085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168789021410852822753132723 253183532116279234129699085)
      ·
        refine ⟨94943824543604712798637157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253183532116279234129699085 94943824543604712798637157)
        ·
          refine ⟨17801967101925883649744467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94943824543604712798637157 17801967101925883649744467)
          ·
            refine ⟨26702950652888825474616701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17801967101925883649744467 26702950652888825474616701)
            ·
              refine ⟨10013606494833309552981263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26702950652888825474616701 10013606494833309552981263)
              ·
                refine ⟨15020409742249964329471895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10013606494833309552981263 15020409742249964329471895)
                ·
                  refine ⟨22530614613374946494207843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15020409742249964329471895 22530614613374946494207843)
                  ·
                    refine ⟨33795921920062419741311765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22530614613374946494207843 33795921920062419741311765)
                    ·
                      refine ⟨1584183840002925925373989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33795921920062419741311765 1584183840002925925373989)
                      ·
                        rfl

theorem cell23_3085187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_3085187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085187 prefixEnd_3085187 := by exact prefixLift 3085187
  have htrace : WordTrace (prefixWord ++ tailWord_3085187) baseStart_3085187 baseEnd_3085187 := by
    simpa [prefixWord, tailWord_3085187, baseEnd_3085187] using wordTrace_append hprefix tailTrace_3085187
  have hstable : (prefixWord ++ tailWord_3085187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085187).length < 2 ^ (prefixWord ++ tailWord_3085187).sum := by decide
  have hdescent : baseEnd_3085187 < baseStart_3085187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085191 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_3085191 : Nat := 118140960795 + 3085191 * 2 ^ 59
def prefixEnd_3085191 : Nat := 4983230072969 + 3 ^ 40 * 3085191 * 2
def baseEnd_3085191 : Nat := 1584185893925543909723971

theorem tailTrace_3085191 : CollatzResearch.WordTrace tailWord_3085191 prefixEnd_3085191 1584185893925543909723971 := by
  unfold tailWord_3085191
  simp only [CollatzResearch.WordTrace]
  refine ⟨112526160165887390518567427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75017440110591593679044951 112526160165887390518567427)
  ·
    refine ⟨168789240248831085777851141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112526160165887390518567427 168789240248831085777851141)
    ·
      refine ⟨31647982546655828583347089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168789240248831085777851141 31647982546655828583347089)
      ·
        refine ⟨23735986909991871437510317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31647982546655828583347089 23735986909991871437510317)
        ·
          refine ⟨8900995091246951789066369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23735986909991871437510317 8900995091246951789066369)
          ·
            refine ⟨6675746318435213841799777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8900995091246951789066369 6675746318435213841799777)
            ·
              refine ⟨5006809738826410381349833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6675746318435213841799777 5006809738826410381349833)
              ·
                refine ⟨3755107304119807786012375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5006809738826410381349833 3755107304119807786012375)
                ·
                  refine ⟨5632660956179711679018563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755107304119807786012375 5632660956179711679018563)
                  ·
                    refine ⟨8448991434269567518527845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5632660956179711679018563 8448991434269567518527845)
                    ·
                      refine ⟨1584185893925543909723971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8448991434269567518527845 1584185893925543909723971)
                      ·
                        rfl

theorem cell23_3085191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_3085191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085191 prefixEnd_3085191 := by exact prefixLift 3085191
  have htrace : WordTrace (prefixWord ++ tailWord_3085191) baseStart_3085191 baseEnd_3085191 := by
    simpa [prefixWord, tailWord_3085191, baseEnd_3085191] using wordTrace_append hprefix tailTrace_3085191
  have hstable : (prefixWord ++ tailWord_3085191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085191).length < 2 ^ (prefixWord ++ tailWord_3085191).sum := by decide
  have hdescent : baseEnd_3085191 < baseStart_3085191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085202 : List Nat := [3, 2, 3, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_3085202 : Nat := 118140960795 + 3085202 * 2 ^ 59
def prefixEnd_3085202 : Nat := 4983230072969 + 3 ^ 40 * 3085202 * 2
def baseEnd_3085202 : Nat := 1584191542212743366686421

theorem tailTrace_3085202 : CollatzResearch.WordTrace tailWord_3085202 prefixEnd_3085202 1584191542212743366686421 := by
  unfold tailWord_3085202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28131640342211884849304465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75017707579231692931478573 28131640342211884849304465)
  ·
    refine ⟨21098730256658913636978349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28131640342211884849304465 21098730256658913636978349)
    ·
      refine ⟨7912023846247092613866881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21098730256658913636978349 7912023846247092613866881)
      ·
        refine ⟨5934017884685319460400161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7912023846247092613866881 5934017884685319460400161)
        ·
          refine ⟨4450513413513989595300121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5934017884685319460400161 4450513413513989595300121)
          ·
            refine ⟨3337885060135492196475091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450513413513989595300121 3337885060135492196475091)
            ·
              refine ⟨5006827590203238294712637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337885060135492196475091 5006827590203238294712637)
              ·
                refine ⟨1877560346326214360517239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5006827590203238294712637 1877560346326214360517239)
                ·
                  refine ⟨2816340519489321540775859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877560346326214360517239 2816340519489321540775859)
                  ·
                    refine ⟨4224510779233982311163789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2816340519489321540775859 4224510779233982311163789)
                    ·
                      refine ⟨1584191542212743366686421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4224510779233982311163789 1584191542212743366686421)
                      ·
                        rfl

theorem cell23_3085202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_3085202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085202 prefixEnd_3085202 := by exact prefixLift 3085202
  have htrace : WordTrace (prefixWord ++ tailWord_3085202) baseStart_3085202 baseEnd_3085202 := by
    simpa [prefixWord, tailWord_3085202, baseEnd_3085202] using wordTrace_append hprefix tailTrace_3085202
  have hstable : (prefixWord ++ tailWord_3085202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085202).length < 2 ^ (prefixWord ++ tailWord_3085202).sum := by decide
  have hdescent : baseEnd_3085202 < baseStart_3085202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085204 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3085204 : Nat := 118140960795 + 3085204 * 2 ^ 59
def prefixEnd_3085204 : Nat := 4983230072969 + 3 ^ 40 * 3085204 * 2
def baseEnd_3085204 : Nat := 1584192569174052358861411

theorem tailTrace_3085204 : CollatzResearch.WordTrace tailWord_3085204 prefixEnd_3085204 1584192569174052358861411 := by
  unfold tailWord_3085204
  simp only [CollatzResearch.WordTrace]
  refine ⟨56263317157420146869395333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75017756209893529159193777 56263317157420146869395333)
  ·
    refine ⟨10549371967016277538011625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56263317157420146869395333 10549371967016277538011625)
    ·
      refine ⟨7912028975262208153508719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10549371967016277538011625 7912028975262208153508719)
      ·
        refine ⟨11868043462893312230263079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7912028975262208153508719 11868043462893312230263079)
        ·
          refine ⟨17802065194339968345394619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11868043462893312230263079 17802065194339968345394619)
          ·
            refine ⟨26703097791509952518091929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17802065194339968345394619 26703097791509952518091929)
            ·
              refine ⟨20027323343632464388568947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26703097791509952518091929 20027323343632464388568947)
              ·
                refine ⟨30040985015448696582853421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20027323343632464388568947 30040985015448696582853421)
                ·
                  refine ⟨11265369380793261218570033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30040985015448696582853421 11265369380793261218570033)
                  ·
                    refine ⟨8449027035594945913927525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11265369380793261218570033 8449027035594945913927525)
                    ·
                      refine ⟨1584192569174052358861411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8449027035594945913927525 1584192569174052358861411)
                      ·
                        rfl

theorem cell23_3085204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3085204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085204 prefixEnd_3085204 := by exact prefixLift 3085204
  have htrace : WordTrace (prefixWord ++ tailWord_3085204) baseStart_3085204 baseEnd_3085204 := by
    simpa [prefixWord, tailWord_3085204, baseEnd_3085204] using wordTrace_append hprefix tailTrace_3085204
  have hstable : (prefixWord ++ tailWord_3085204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085204).length < 2 ^ (prefixWord ++ tailWord_3085204).sum := by decide
  have hdescent : baseEnd_3085204 < baseStart_3085204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085225 : List Nat := [1, 2, 1, 1, 1, 1, 9, 2, 1, 2, 2]
def baseStart_3085225 : Nat := 118140960795 + 3085225 * 2 ^ 59
def prefixEnd_3085225 : Nat := 4983230072969 + 3 ^ 40 * 3085225 * 2
def baseEnd_3085225 : Nat := 1584203352267796776698815

theorem tailTrace_3085225 : CollatzResearch.WordTrace tailWord_3085225 prefixEnd_3085225 1584203352267796776698815 := by
  unfold tailWord_3085225
  simp only [CollatzResearch.WordTrace]
  refine ⟨112527400247764214325305129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75018266831842809550203419 112527400247764214325305129)
  ·
    refine ⟨84395550185823160743978847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112527400247764214325305129 84395550185823160743978847)
    ·
      refine ⟨126593325278734741115968271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84395550185823160743978847 126593325278734741115968271)
      ·
        refine ⟨189889987918102111673952407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126593325278734741115968271 189889987918102111673952407)
        ·
          refine ⟨284834981877153167510928611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189889987918102111673952407 284834981877153167510928611)
          ·
            refine ⟨427252472815729751266392917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284834981877153167510928611 427252472815729751266392917)
            ·
              refine ⟨2503432457904666511326521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 427252472815729751266392917 2503432457904666511326521)
              ·
                refine ⟨1877574343428499883494891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503432457904666511326521 1877574343428499883494891)
                ·
                  refine ⟨2816361515142749825242337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877574343428499883494891 2816361515142749825242337)
                  ·
                    refine ⟨2112271136357062368931753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2816361515142749825242337 2112271136357062368931753)
                    ·
                      refine ⟨1584203352267796776698815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112271136357062368931753 1584203352267796776698815)
                      ·
                        rfl

theorem cell23_3085225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 2, 2].length) (baseStart_3085225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085225 prefixEnd_3085225 := by exact prefixLift 3085225
  have htrace : WordTrace (prefixWord ++ tailWord_3085225) baseStart_3085225 baseEnd_3085225 := by
    simpa [prefixWord, tailWord_3085225, baseEnd_3085225] using wordTrace_append hprefix tailTrace_3085225
  have hstable : (prefixWord ++ tailWord_3085225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085225).length < 2 ^ (prefixWord ++ tailWord_3085225).sum := by decide
  have hdescent : baseEnd_3085225 < baseStart_3085225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085234 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_3085234 : Nat := 118140960795 + 3085234 * 2 ^ 59
def prefixEnd_3085234 : Nat := 4983230072969 + 3 ^ 40 * 3085234 * 2
def baseEnd_3085234 : Nat := 1584207973593687241486273

theorem tailTrace_3085234 : CollatzResearch.WordTrace tailWord_3085234 prefixEnd_3085234 1584207973593687241486273 := by
  unfold tailWord_3085234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28131932126182902215595689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75018485669821072574921837 28131932126182902215595689)
  ·
    refine ⟨21098949094637176661696767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28131932126182902215595689 21098949094637176661696767)
    ·
      refine ⟨31648423641955764992545151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21098949094637176661696767 31648423641955764992545151)
      ·
        refine ⟨47472635462933647488817727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31648423641955764992545151 47472635462933647488817727)
        ·
          refine ⟨71208953194400471233226591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47472635462933647488817727 71208953194400471233226591)
          ·
            refine ⟨106813429791600706849839887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71208953194400471233226591 106813429791600706849839887)
            ·
              refine ⟨160220144687401060274759831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106813429791600706849839887 160220144687401060274759831)
              ·
                refine ⟨240330217031101590412139747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160220144687401060274759831 240330217031101590412139747)
                ·
                  refine ⟨360495325546652385618209621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240330217031101590412139747 360495325546652385618209621)
                  ·
                    refine ⟨2112277298124916321981697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 360495325546652385618209621 2112277298124916321981697)
                    ·
                      refine ⟨1584207973593687241486273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112277298124916321981697 1584207973593687241486273)
                      ·
                        rfl

theorem cell23_3085234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_3085234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085234 prefixEnd_3085234 := by exact prefixLift 3085234
  have htrace : WordTrace (prefixWord ++ tailWord_3085234) baseStart_3085234 baseEnd_3085234 := by
    simpa [prefixWord, tailWord_3085234, baseEnd_3085234] using wordTrace_append hprefix tailTrace_3085234
  have hstable : (prefixWord ++ tailWord_3085234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085234).length < 2 ^ (prefixWord ++ tailWord_3085234).sum := by decide
  have hdescent : baseEnd_3085234 < baseStart_3085234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085245 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_3085245 : Nat := 118140960795 + 3085245 * 2 ^ 59
def prefixEnd_3085245 : Nat := 4983230072969 + 3 ^ 40 * 3085245 * 2
def baseEnd_3085245 : Nat := 1584213621880886698448723

theorem tailTrace_3085245 : CollatzResearch.WordTrace tailWord_3085245 prefixEnd_3085245 1584213621880886698448723 := by
  unfold tailWord_3085245
  simp only [CollatzResearch.WordTrace]
  refine ⟨112528129707691757741033189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75018753138461171827355459 112528129707691757741033189)
  ·
    refine ⟨21099024320192204576443723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112528129707691757741033189 21099024320192204576443723)
    ·
      refine ⟨31648536480288306864665585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21099024320192204576443723 31648536480288306864665585)
      ·
        refine ⟨23736402360216230148499189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31648536480288306864665585 23736402360216230148499189)
        ·
          refine ⟨2225287721270271576421799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23736402360216230148499189 2225287721270271576421799)
          ·
            refine ⟨3337931581905407364632699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225287721270271576421799 3337931581905407364632699)
            ·
              refine ⟨5006897372858111046949049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337931581905407364632699 5006897372858111046949049)
              ·
                refine ⟨3755173029643583285211787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5006897372858111046949049 3755173029643583285211787)
                ·
                  refine ⟨5632759544465374927817681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755173029643583285211787 5632759544465374927817681)
                  ·
                    refine ⟨4224569658349031195863261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5632759544465374927817681 4224569658349031195863261)
                    ·
                      refine ⟨1584213621880886698448723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4224569658349031195863261 1584213621880886698448723)
                      ·
                        rfl

theorem cell23_3085245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_3085245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085245 prefixEnd_3085245 := by exact prefixLift 3085245
  have htrace : WordTrace (prefixWord ++ tailWord_3085245) baseStart_3085245 baseEnd_3085245 := by
    simpa [prefixWord, tailWord_3085245, baseEnd_3085245] using wordTrace_append hprefix tailTrace_3085245
  have hstable : (prefixWord ++ tailWord_3085245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085245).length < 2 ^ (prefixWord ++ tailWord_3085245).sum := by decide
  have hdescent : baseEnd_3085245 < baseStart_3085245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085247 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_3085247 : Nat := 118140960795 + 3085247 * 2 ^ 59
def prefixEnd_3085247 : Nat := 4983230072969 + 3 ^ 40 * 3085247 * 2
def baseEnd_3085247 : Nat := 1584214648842195690623713

theorem tailTrace_3085247 : CollatzResearch.WordTrace tailWord_3085247 prefixEnd_3085247 1584214648842195690623713 := by
  unfold tailWord_3085247
  simp only [CollatzResearch.WordTrace]
  refine ⟨112528202653684512082605995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75018801769123008055070663 112528202653684512082605995)
  ·
    refine ⟨168792303980526768123908993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112528202653684512082605995 168792303980526768123908993)
    ·
      refine ⟨126594227985395076092931745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168792303980526768123908993 126594227985395076092931745)
      ·
        refine ⟨94945670989046307069698809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126594227985395076092931745 94945670989046307069698809)
        ·
          refine ⟨71209253241784730302274107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94945670989046307069698809 71209253241784730302274107)
          ·
            refine ⟨106813879862677095453411161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71209253241784730302274107 106813879862677095453411161)
            ·
              refine ⟨80110409897007821590058371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106813879862677095453411161 80110409897007821590058371)
              ·
                refine ⟨120165614845511732385087557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80110409897007821590058371 120165614845511732385087557)
                ·
                  refine ⟨22531052783533449822203917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120165614845511732385087557 22531052783533449822203917)
                  ·
                    refine ⟨8449144793825043683326469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22531052783533449822203917 8449144793825043683326469)
                    ·
                      refine ⟨1584214648842195690623713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8449144793825043683326469 1584214648842195690623713)
                      ·
                        rfl

theorem cell23_3085247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_3085247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085247 prefixEnd_3085247 := by exact prefixLift 3085247
  have htrace : WordTrace (prefixWord ++ tailWord_3085247) baseStart_3085247 baseEnd_3085247 := by
    simpa [prefixWord, tailWord_3085247, baseEnd_3085247] using wordTrace_append hprefix tailTrace_3085247
  have hstable : (prefixWord ++ tailWord_3085247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085247).length < 2 ^ (prefixWord ++ tailWord_3085247).sum := by decide
  have hdescent : baseEnd_3085247 < baseStart_3085247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085327 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_3085327 : Nat := 118140960795 + 3085327 * 2 ^ 59
def prefixEnd_3085327 : Nat := 4983230072969 + 3 ^ 40 * 3085327 * 2
def baseEnd_3085327 : Nat := 1584255727294555377623345

theorem tailTrace_3085327 : CollatzResearch.WordTrace tailWord_3085327 prefixEnd_3085327 1584255727294555377623345 := by
  unfold tailWord_3085327
  simp only [CollatzResearch.WordTrace]
  refine ⟨112531120493394685745518235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75020746995596457163678823 112531120493394685745518235)
  ·
    refine ⟨168796680740092028618277353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112531120493394685745518235 168796680740092028618277353)
    ·
      refine ⟨126597510555069021463708015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168796680740092028618277353 126597510555069021463708015)
      ·
        refine ⟨189896265832603532195562023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126597510555069021463708015 189896265832603532195562023)
        ·
          refine ⟨284844398748905298293343035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189896265832603532195562023 284844398748905298293343035)
          ·
            refine ⟨427266598123357947440014553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284844398748905298293343035 427266598123357947440014553)
            ·
              refine ⟨320449948592518460580010915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427266598123357947440014553 320449948592518460580010915)
              ·
                refine ⟨480674922888777690870016373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320449948592518460580010915 480674922888777690870016373)
                ·
                  refine ⟨45063274020822908519064035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480674922888777690870016373 45063274020822908519064035)
                  ·
                    refine ⟨67594911031234362778596053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45063274020822908519064035 67594911031234362778596053)
                    ·
                      refine ⟨1584255727294555377623345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67594911031234362778596053 1584255727294555377623345)
                      ·
                        rfl

theorem cell23_3085327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_3085327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085327 prefixEnd_3085327 := by exact prefixLift 3085327
  have htrace : WordTrace (prefixWord ++ tailWord_3085327) baseStart_3085327 baseEnd_3085327 := by
    simpa [prefixWord, tailWord_3085327, baseEnd_3085327] using wordTrace_append hprefix tailTrace_3085327
  have hstable : (prefixWord ++ tailWord_3085327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085327).length < 2 ^ (prefixWord ++ tailWord_3085327).sum := by decide
  have hdescent : baseEnd_3085327 < baseStart_3085327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085351 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3085351 : Nat := 118140960795 + 3085351 * 2 ^ 59
def prefixEnd_3085351 : Nat := 4983230072969 + 3 ^ 40 * 3085351 * 2
def baseEnd_3085351 : Nat := 528089350276754427907745

theorem tailTrace_3085351 : CollatzResearch.WordTrace tailWord_3085351 prefixEnd_3085351 528089350276754427907745 := by
  unfold tailWord_3085351
  simp only [CollatzResearch.WordTrace]
  refine ⟨112531995845307737844391907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75021330563538491896261271 112531995845307737844391907)
  ·
    refine ⟨168797993767961606766587861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112531995845307737844391907 168797993767961606766587861)
    ·
      refine ⟨3956202978936600158591903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 168797993767961606766587861 3956202978936600158591903)
      ·
        refine ⟨5934304468404900237887855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956202978936600158591903 5934304468404900237887855)
        ·
          refine ⟨8901456702607350356831783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934304468404900237887855 8901456702607350356831783)
          ·
            refine ⟨13352185053911025535247675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901456702607350356831783 13352185053911025535247675)
            ·
              refine ⟨20028277580866538302871513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13352185053911025535247675 20028277580866538302871513)
              ·
                refine ⟨15021208185649903727153635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20028277580866538302871513 15021208185649903727153635)
                ·
                  refine ⟨22531812278474855590730453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15021208185649903727153635 22531812278474855590730453)
                  ·
                    refine ⟨528089350276754427907745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22531812278474855590730453 528089350276754427907745)
                    ·
                      rfl

theorem cell23_3085351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3085351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085351 prefixEnd_3085351 := by exact prefixLift 3085351
  have htrace : WordTrace (prefixWord ++ tailWord_3085351) baseStart_3085351 baseEnd_3085351 := by
    simpa [prefixWord, tailWord_3085351, baseEnd_3085351] using wordTrace_append hprefix tailTrace_3085351
  have hstable : (prefixWord ++ tailWord_3085351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085351).length < 2 ^ (prefixWord ++ tailWord_3085351).sum := by decide
  have hdescent : baseEnd_3085351 < baseStart_3085351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085482 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3085482 : Nat := 118140960795 + 3085482 * 2 ^ 59
def prefixEnd_3085482 : Nat := 4983230072969 + 3 ^ 40 * 3085482 * 2
def baseEnd_3085482 : Nat := 1584335316796002271185133

theorem tailTrace_3085482 : CollatzResearch.WordTrace tailWord_3085482 prefixEnd_3085482 1584335316796002271185133 := by
  unfold tailWord_3085482
  simp only [CollatzResearch.WordTrace]
  refine ⟨28134193451958286804352675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75024515871888764811607133 28134193451958286804352675)
  ·
    refine ⟨42201290177937430206529013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28134193451958286804352675 42201290177937430206529013)
    ·
      refine ⟨3956370954181634081862095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42201290177937430206529013 3956370954181634081862095)
      ·
        refine ⟨5934556431272451122793143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956370954181634081862095 5934556431272451122793143)
        ·
          refine ⟨8901834646908676684189715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934556431272451122793143 8901834646908676684189715)
          ·
            refine ⟨13352751970363015026284573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901834646908676684189715 13352751970363015026284573)
            ·
              refine ⟨5007281988886130634856715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13352751970363015026284573 5007281988886130634856715)
              ·
                refine ⟨7510922983329195952285073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5007281988886130634856715 7510922983329195952285073)
                ·
                  refine ⟨5633192237496896964213805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7510922983329195952285073 5633192237496896964213805)
                  ·
                    refine ⟨2112447089061336361580177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5633192237496896964213805 2112447089061336361580177)
                    ·
                      refine ⟨1584335316796002271185133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112447089061336361580177 1584335316796002271185133)
                      ·
                        rfl

theorem cell23_3085482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3085482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085482 prefixEnd_3085482 := by exact prefixLift 3085482
  have htrace : WordTrace (prefixWord ++ tailWord_3085482) baseStart_3085482 baseEnd_3085482 := by
    simpa [prefixWord, tailWord_3085482, baseEnd_3085482] using wordTrace_append hprefix tailTrace_3085482
  have hstable : (prefixWord ++ tailWord_3085482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085482).length < 2 ^ (prefixWord ++ tailWord_3085482).sum := by decide
  have hdescent : baseEnd_3085482 < baseStart_3085482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085491 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 4]
def baseStart_3085491 : Nat := 118140960795 + 3085491 * 2 ^ 59
def prefixEnd_3085491 : Nat := 4983230072969 + 3 ^ 40 * 3085491 * 2
def baseEnd_3085491 : Nat := 1584339938121892735972591

theorem tailTrace_3085491 : CollatzResearch.WordTrace tailWord_3085491 prefixEnd_3085491 1584339938121892735972591 := by
  unfold tailWord_3085491
  simp only [CollatzResearch.WordTrace]
  refine ⟨112537102064800541754488327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75024734709867027836325551 112537102064800541754488327)
  ·
    refine ⟨168805653097200812631732491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112537102064800541754488327 168805653097200812631732491)
    ·
      refine ⟨253208479645801218947598737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168805653097200812631732491 253208479645801218947598737)
      ·
        refine ⟨189906359734350914210699053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253208479645801218947598737 189906359734350914210699053)
        ·
          refine ⟨71214884900381592829012145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189906359734350914210699053 71214884900381592829012145)
          ·
            refine ⟨53411163675286194621759109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71214884900381592829012145 53411163675286194621759109)
            ·
              refine ⟨10014593189116161491579833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53411163675286194621759109 10014593189116161491579833)
              ·
                refine ⟨7510944891837121118684875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10014593189116161491579833 7510944891837121118684875)
                ·
                  refine ⟨11266417337755681678027313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7510944891837121118684875 11266417337755681678027313)
                  ·
                    refine ⟨8449813003316761258520485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11266417337755681678027313 8449813003316761258520485)
                    ·
                      refine ⟨1584339938121892735972591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8449813003316761258520485 1584339938121892735972591)
                      ·
                        rfl

theorem cell23_3085491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_3085491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085491 prefixEnd_3085491 := by exact prefixLift 3085491
  have htrace : WordTrace (prefixWord ++ tailWord_3085491) baseStart_3085491 baseEnd_3085491 := by
    simpa [prefixWord, tailWord_3085491, baseEnd_3085491] using wordTrace_append hprefix tailTrace_3085491
  have hstable : (prefixWord ++ tailWord_3085491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085491).length < 2 ^ (prefixWord ++ tailWord_3085491).sum := by decide
  have hdescent : baseEnd_3085491 < baseStart_3085491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085505 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3085505 : Nat := 118140960795 + 3085505 * 2 ^ 59
def prefixEnd_3085505 : Nat := 4983230072969 + 3 ^ 40 * 3085505 * 2
def baseEnd_3085505 : Nat := 528115708950351893732509

theorem tailTrace_3085505 : CollatzResearch.WordTrace tailWord_3085505 prefixEnd_3085505 528115708950351893732509 := by
  unfold tailWord_3085505
  simp only [CollatzResearch.WordTrace]
  refine ⟨112537612686749822145497969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75025075124499881430331979 112537612686749822145497969)
  ·
    refine ⟨84403209515062366609123477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112537612686749822145497969 84403209515062366609123477)
    ·
      refine ⟨3956400446018548434802663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84403209515062366609123477 3956400446018548434802663)
      ·
        refine ⟨5934600669027822652203995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956400446018548434802663 5934600669027822652203995)
        ·
          refine ⟨8901901003541733978305993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934600669027822652203995 8901901003541733978305993)
          ·
            refine ⟨6676425752656300483729495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8901901003541733978305993 6676425752656300483729495)
            ·
              refine ⟨10014638628984450725594243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676425752656300483729495 10014638628984450725594243)
              ·
                refine ⟨15021957943476676088391365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10014638628984450725594243 15021957943476676088391365)
                ·
                  refine ⟨2816617114401876766573381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15021957943476676088391365 2816617114401876766573381)
                  ·
                    refine ⟨528115708950351893732509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2816617114401876766573381 528115708950351893732509)
                    ·
                      rfl

theorem cell23_3085505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3085505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085505 prefixEnd_3085505 := by exact prefixLift 3085505
  have htrace : WordTrace (prefixWord ++ tailWord_3085505) baseStart_3085505 baseEnd_3085505 := by
    simpa [prefixWord, tailWord_3085505, baseEnd_3085505] using wordTrace_append hprefix tailTrace_3085505
  have hstable : (prefixWord ++ tailWord_3085505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085505).length < 2 ^ (prefixWord ++ tailWord_3085505).sum := by decide
  have hdescent : baseEnd_3085505 < baseStart_3085505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085511 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_3085511 : Nat := 118140960795 + 3085511 * 2 ^ 59
def prefixEnd_3085511 : Nat := 4983230072969 + 3 ^ 40 * 3085511 * 2
def baseEnd_3085511 : Nat := 1584350207734982657722499

theorem tailTrace_3085511 : CollatzResearch.WordTrace tailWord_3085511 prefixEnd_3085511 1584350207734982657722499 := by
  unfold tailWord_3085511
  simp only [CollatzResearch.WordTrace]
  refine ⟨112537831524728085170216387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75025221016485390113477591 112537831524728085170216387)
  ·
    refine ⟨168806747287092127755324581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112537831524728085170216387 168806747287092127755324581)
    ·
      refine ⟨31651265116329773954123359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168806747287092127755324581 31651265116329773954123359)
      ·
        refine ⟨47476897674494660931185039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31651265116329773954123359 47476897674494660931185039)
        ·
          refine ⟨71215346511741991396777559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47476897674494660931185039 71215346511741991396777559)
          ·
            refine ⟨106823019767612987095166339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71215346511741991396777559 106823019767612987095166339)
            ·
              refine ⟨160234529651419480642749509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106823019767612987095166339 160234529651419480642749509)
              ·
                refine ⟨30043974309641152620515533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160234529651419480642749509 30043974309641152620515533)
                ·
                  refine ⟨11266490366115432232693325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30043974309641152620515533 11266490366115432232693325)
                  ·
                    refine ⟨4224933887293287087259997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11266490366115432232693325 4224933887293287087259997)
                    ·
                      refine ⟨1584350207734982657722499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4224933887293287087259997 1584350207734982657722499)
                      ·
                        rfl

theorem cell23_3085511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_3085511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085511 prefixEnd_3085511 := by exact prefixLift 3085511
  have htrace : WordTrace (prefixWord ++ tailWord_3085511) baseStart_3085511 baseEnd_3085511 := by
    simpa [prefixWord, tailWord_3085511, baseEnd_3085511] using wordTrace_append hprefix tailTrace_3085511
  have hstable : (prefixWord ++ tailWord_3085511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085511).length < 2 ^ (prefixWord ++ tailWord_3085511).sum := by decide
  have hdescent : baseEnd_3085511 < baseStart_3085511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085512 : List Nat := [2, 1, 3, 1, 2, 1, 4, 4, 1, 2, 2]
def baseStart_3085512 : Nat := 118140960795 + 3085512 * 2 ^ 59
def prefixEnd_3085512 : Nat := 4983230072969 + 3 ^ 40 * 3085512 * 2
def baseEnd_3085512 : Nat := 1584350721215637153809995

theorem tailTrace_3085512 : CollatzResearch.WordTrace tailWord_3085512 prefixEnd_3085512 1584350721215637153809995 := by
  unfold tailWord_3085512
  simp only [CollatzResearch.WordTrace]
  refine ⟨56268933998862231170501395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75025245331816308227335193 56268933998862231170501395)
  ·
    refine ⟨84403400998293346755752093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56268933998862231170501395 84403400998293346755752093)
    ·
      refine ⟨31651275374360005033407035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84403400998293346755752093 31651275374360005033407035)
      ·
        refine ⟨47476913061540007550110553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31651275374360005033407035 47476913061540007550110553)
        ·
          refine ⟨35607684796155005662582915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47476913061540007550110553 35607684796155005662582915)
          ·
            refine ⟨53411527194232508493874373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35607684796155005662582915 53411527194232508493874373)
            ·
              refine ⟨10014661348918595342601445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53411527194232508493874373 10014661348918595342601445)
              ·
                refine ⟨1877749002922236626737771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10014661348918595342601445 1877749002922236626737771)
                ·
                  refine ⟨2816623504383354940106657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877749002922236626737771 2816623504383354940106657)
                  ·
                    refine ⟨2112467628287516205079993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2816623504383354940106657 2112467628287516205079993)
                    ·
                      refine ⟨1584350721215637153809995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112467628287516205079993 1584350721215637153809995)
                      ·
                        rfl

theorem cell23_3085512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_3085512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085512 prefixEnd_3085512 := by exact prefixLift 3085512
  have htrace : WordTrace (prefixWord ++ tailWord_3085512) baseStart_3085512 baseEnd_3085512 := by
    simpa [prefixWord, tailWord_3085512, baseEnd_3085512] using wordTrace_append hprefix tailTrace_3085512
  have hstable : (prefixWord ++ tailWord_3085512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085512).length < 2 ^ (prefixWord ++ tailWord_3085512).sum := by decide
  have hdescent : baseEnd_3085512 < baseStart_3085512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085525 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3085525 : Nat := 118140960795 + 3085525 * 2 ^ 59
def prefixEnd_3085525 : Nat := 4983230072969 + 3 ^ 40 * 3085525 * 2
def baseEnd_3085525 : Nat := 1584357396464145602947435

theorem tailTrace_3085525 : CollatzResearch.WordTrace tailWord_3085525 prefixEnd_3085525 1584357396464145602947435 := by
  unfold tailWord_3085525
  simp only [CollatzResearch.WordTrace]
  refine ⟨112538342146677365561226029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75025561431118243707484019 112538342146677365561226029)
  ·
    refine ⟨42201878305004012085459761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112538342146677365561226029 42201878305004012085459761)
    ·
      refine ⟨31651408728753009064094821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42201878305004012085459761 31651408728753009064094821)
      ·
        refine ⟨5934639136641189199517779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31651408728753009064094821 5934639136641189199517779)
        ·
          refine ⟨8901958704961783799276669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934639136641189199517779 8901958704961783799276669)
          ·
            refine ⟨3338234514360668924728751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8901958704961783799276669 3338234514360668924728751)
            ·
              refine ⟨5007351771541003387093127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338234514360668924728751 5007351771541003387093127)
              ·
                refine ⟨7511027657311505080639691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5007351771541003387093127 7511027657311505080639691)
                ·
                  refine ⟨11266541485967257620959537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511027657311505080639691 11266541485967257620959537)
                  ·
                    refine ⟨8449906114475443215719653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11266541485967257620959537 8449906114475443215719653)
                    ·
                      refine ⟨1584357396464145602947435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8449906114475443215719653 1584357396464145602947435)
                      ·
                        rfl

theorem cell23_3085525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3085525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085525 prefixEnd_3085525 := by exact prefixLift 3085525
  have htrace : WordTrace (prefixWord ++ tailWord_3085525) baseStart_3085525 baseEnd_3085525 := by
    simpa [prefixWord, tailWord_3085525, baseEnd_3085525] using wordTrace_append hprefix tailTrace_3085525
  have hstable : (prefixWord ++ tailWord_3085525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085525).length < 2 ^ (prefixWord ++ tailWord_3085525).sum := by decide
  have hdescent : baseEnd_3085525 < baseStart_3085525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085555 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 1, 3, 2]
def baseStart_3085555 : Nat := 118140960795 + 3085555 * 2 ^ 59
def prefixEnd_3085555 : Nat := 4983230072969 + 3 ^ 40 * 3085555 * 2
def baseEnd_3085555 : Nat := 1584372800883780485572297

theorem tailTrace_3085555 : CollatzResearch.WordTrace tailWord_3085555 prefixEnd_3085555 1584372800883780485572297 := by
  unfold tailWord_3085555
  simp only [CollatzResearch.WordTrace]
  refine ⟨112539436336568680684818119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75026290891045787123212079 112539436336568680684818119)
  ·
    refine ⟨168809154504853021027227179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112539436336568680684818119 168809154504853021027227179)
    ·
      refine ⟨253213731757279531540840769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168809154504853021027227179 253213731757279531540840769)
      ·
        refine ⟨189910298817959648655630577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253213731757279531540840769 189910298817959648655630577)
        ·
          refine ⟨142432724113469736491722933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189910298817959648655630577 142432724113469736491722933)
          ·
            refine ⟨13353067885637787796099025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142432724113469736491722933 13353067885637787796099025)
            ·
              refine ⟨10014800914228340847074269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13353067885637787796099025 10014800914228340847074269)
              ·
                refine ⟨3755550342835627817652851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10014800914228340847074269 3755550342835627817652851)
                ·
                  refine ⟨5633325514253441726479277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755550342835627817652851 5633325514253441726479277)
                  ·
                    refine ⟨2112497067845040647429729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5633325514253441726479277 2112497067845040647429729)
                    ·
                      refine ⟨1584372800883780485572297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112497067845040647429729 1584372800883780485572297)
                      ·
                        rfl

theorem cell23_3085555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 3, 2].length) (baseStart_3085555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085555 prefixEnd_3085555 := by exact prefixLift 3085555
  have htrace : WordTrace (prefixWord ++ tailWord_3085555) baseStart_3085555 baseEnd_3085555 := by
    simpa [prefixWord, tailWord_3085555, baseEnd_3085555] using wordTrace_append hprefix tailTrace_3085555
  have hstable : (prefixWord ++ tailWord_3085555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085555).length < 2 ^ (prefixWord ++ tailWord_3085555).sum := by decide
  have hdescent : baseEnd_3085555 < baseStart_3085555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085591 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 9]
def baseStart_3085591 : Nat := 118140960795 + 3085591 * 2 ^ 59
def prefixEnd_3085591 : Nat := 4983230072969 + 3 ^ 40 * 3085591 * 2
def baseEnd_3085591 : Nat := 176043476243038038302459

theorem tailTrace_3085591 : CollatzResearch.WordTrace tailWord_3085591 prefixEnd_3085591 176043476243038038302459 := by
  unfold tailWord_3085591
  simp only [CollatzResearch.WordTrace]
  refine ⟨112540749364438258833128627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75027166242958839222085751 112540749364438258833128627)
  ·
    refine ⟨168811124046657388249692941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112540749364438258833128627 168811124046657388249692941)
    ·
      refine ⟨63304171517496520593634853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168811124046657388249692941 63304171517496520593634853)
      ·
        refine ⟨11869532159530597611306535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63304171517496520593634853 11869532159530597611306535)
        ·
          refine ⟨17804298239295896416959803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11869532159530597611306535 17804298239295896416959803)
          ·
            refine ⟨26706447358943844625439705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17804298239295896416959803 26706447358943844625439705)
            ·
              refine ⟨20029835519207883469079779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26706447358943844625439705 20029835519207883469079779)
              ·
                refine ⟨30044753278811825203619669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20029835519207883469079779 30044753278811825203619669)
                ·
                  refine ⟨176043476243038038302459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30044753278811825203619669 176043476243038038302459)
                  ·
                    rfl

theorem cell23_3085591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 9].length) (baseStart_3085591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085591 prefixEnd_3085591 := by exact prefixLift 3085591
  have htrace : WordTrace (prefixWord ++ tailWord_3085591) baseStart_3085591 baseEnd_3085591 := by
    simpa [prefixWord, tailWord_3085591, baseEnd_3085591] using wordTrace_append hprefix tailTrace_3085591
  have hstable : (prefixWord ++ tailWord_3085591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085591).length < 2 ^ (prefixWord ++ tailWord_3085591).sum := by decide
  have hdescent : baseEnd_3085591 < baseStart_3085591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085602 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_3085602 : Nat := 118140960795 + 3085602 * 2 ^ 59
def prefixEnd_3085602 : Nat := 4983230072969 + 3 ^ 40 * 3085602 * 2
def baseEnd_3085602 : Nat := 1584396934474541801684581

theorem tailTrace_3085602 : CollatzResearch.WordTrace tailWord_3085602 prefixEnd_3085602 1584396934474541801684581 := by
  unfold tailWord_3085602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28135287641849601927944765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75027433711598938474519373 28135287641849601927944765)
  ·
    refine ⟨10550732865693600722979287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28135287641849601927944765 10550732865693600722979287)
    ·
      refine ⟨15826099298540401084468931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10550732865693600722979287 15826099298540401084468931)
      ·
        refine ⟨23739148947810601626703397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15826099298540401084468931 23739148947810601626703397)
        ·
          refine ⟨4451090427714487805006887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23739148947810601626703397 4451090427714487805006887)
          ·
            refine ⟨6676635641571731707510331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451090427714487805006887 6676635641571731707510331)
            ·
              refine ⟨10014953462357597561265497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676635641571731707510331 10014953462357597561265497)
              ·
                refine ⟨7511215096768198170949123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10014953462357597561265497 7511215096768198170949123)
                ·
                  refine ⟨11266822645152297256423685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511215096768198170949123 11266822645152297256423685)
                  ·
                    refine ⟨2112529245966055735579441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11266822645152297256423685 2112529245966055735579441)
                    ·
                      refine ⟨1584396934474541801684581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112529245966055735579441 1584396934474541801684581)
                      ·
                        rfl

theorem cell23_3085602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_3085602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085602 prefixEnd_3085602 := by exact prefixLift 3085602
  have htrace : WordTrace (prefixWord ++ tailWord_3085602) baseStart_3085602 baseEnd_3085602 := by
    simpa [prefixWord, tailWord_3085602, baseEnd_3085602] using wordTrace_append hprefix tailTrace_3085602
  have hstable : (prefixWord ++ tailWord_3085602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085602).length < 2 ^ (prefixWord ++ tailWord_3085602).sum := by decide
  have hdescent : baseEnd_3085602 < baseStart_3085602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085655 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 2, 5]
def baseStart_3085655 : Nat := 118140960795 + 3085655 * 2 ^ 59
def prefixEnd_3085655 : Nat := 4983230072969 + 3 ^ 40 * 3085655 * 2
def baseEnd_3085655 : Nat := 528141382983076698107279

theorem tailTrace_3085655 : CollatzResearch.WordTrace tailWord_3085655 prefixEnd_3085655 528141382983076698107279 := by
  unfold tailWord_3085655
  simp only [CollatzResearch.WordTrace]
  refine ⟨112543083636206397763458419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75028722424137598508972279 112543083636206397763458419)
  ·
    refine ⟨168814625454309596645187629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112543083636206397763458419 168814625454309596645187629)
    ·
      refine ⟨63305484545366098741945361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168814625454309596645187629 63305484545366098741945361)
      ·
        refine ⟨47479113409024574056459021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63305484545366098741945361 47479113409024574056459021)
        ·
          refine ⟨17804667528384215271172133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47479113409024574056459021 17804667528384215271172133)
          ·
            refine ⟨3338375161572040363344775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17804667528384215271172133 3338375161572040363344775)
            ·
              refine ⟨5007562742358060545017163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338375161572040363344775 5007562742358060545017163)
              ·
                refine ⟨7511344113537090817525745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5007562742358060545017163 7511344113537090817525745)
                ·
                  refine ⟨5633508085152818113144309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7511344113537090817525745 5633508085152818113144309)
                  ·
                    refine ⟨528141382983076698107279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5633508085152818113144309 528141382983076698107279)
                    ·
                      rfl

theorem cell23_3085655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_3085655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085655 prefixEnd_3085655 := by exact prefixLift 3085655
  have htrace : WordTrace (prefixWord ++ tailWord_3085655) baseStart_3085655 baseEnd_3085655 := by
    simpa [prefixWord, tailWord_3085655, baseEnd_3085655] using wordTrace_append hprefix tailTrace_3085655
  have hstable : (prefixWord ++ tailWord_3085655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085655).length < 2 ^ (prefixWord ++ tailWord_3085655).sum := by decide
  have hdescent : baseEnd_3085655 < baseStart_3085655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085708 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_3085708 : Nat := 118140960795 + 3085708 * 2 ^ 59
def prefixEnd_3085708 : Nat := 4983230072969 + 3 ^ 40 * 3085708 * 2
def baseEnd_3085708 : Nat := 1584451363423918386959093

theorem tailTrace_3085708 : CollatzResearch.WordTrace tailWord_3085708 prefixEnd_3085708 1584451363423918386959093 := by
  unfold tailWord_3085708
  simp only [CollatzResearch.WordTrace]
  refine ⟨56272508352507193907568889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75030011136676258543425185 56272508352507193907568889)
  ·
    refine ⟨42204381264380395430676667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56272508352507193907568889 42204381264380395430676667)
    ·
      refine ⟨63306571896570593146015001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42204381264380395430676667 63306571896570593146015001)
      ·
        refine ⟨47479928922427944859511251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63306571896570593146015001 47479928922427944859511251)
        ·
          refine ⟨71219893383641917289266877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47479928922427944859511251 71219893383641917289266877)
          ·
            refine ⟨26707460018865718983475079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71219893383641917289266877 26707460018865718983475079)
            ·
              refine ⟨40061190028298578475212619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26707460018865718983475079 40061190028298578475212619)
              ·
                refine ⟨60091785042447867712818929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40061190028298578475212619 60091785042447867712818929)
                ·
                  refine ⟨45068838781835900784614197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60091785042447867712818929 45068838781835900784614197)
                  ·
                    refine ⟨4225203635797115698557581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45068838781835900784614197 4225203635797115698557581)
                    ·
                      refine ⟨1584451363423918386959093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4225203635797115698557581 1584451363423918386959093)
                      ·
                        rfl

theorem cell23_3085708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_3085708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085708 prefixEnd_3085708 := by exact prefixLift 3085708
  have htrace : WordTrace (prefixWord ++ tailWord_3085708) baseStart_3085708 baseEnd_3085708 := by
    simpa [prefixWord, tailWord_3085708, baseEnd_3085708] using wordTrace_append hprefix tailTrace_3085708
  have hstable : (prefixWord ++ tailWord_3085708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085708).length < 2 ^ (prefixWord ++ tailWord_3085708).sum := by decide
  have hdescent : baseEnd_3085708 < baseStart_3085708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085736 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3085736 : Nat := 118140960795 + 3085736 * 2 ^ 59
def prefixEnd_3085736 : Nat := 4983230072969 + 3 ^ 40 * 3085736 * 2
def baseEnd_3085736 : Nat := 528155246960748092469655

theorem tailTrace_3085736 : CollatzResearch.WordTrace tailWord_3085736 prefixEnd_3085736 528155246960748092469655 := by
  unfold tailWord_3085736
  simp only [CollatzResearch.WordTrace]
  refine ⟨56273018974456474298578531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75030691965941965731438041 56273018974456474298578531)
  ·
    refine ⟨84409528461684711447867797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56273018974456474298578531 84409528461684711447867797)
    ·
      refine ⟨3956696646641470849118803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84409528461684711447867797 3956696646641470849118803)
      ·
        refine ⟨5935044969962206273678205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956696646641470849118803 5935044969962206273678205)
        ·
          refine ⟨2225641863735827352629327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5935044969962206273678205 2225641863735827352629327)
          ·
            refine ⟨3338462795603741028943991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225641863735827352629327 3338462795603741028943991)
            ·
              refine ⟨5007694193405611543415987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338462795603741028943991 5007694193405611543415987)
              ·
                refine ⟨7511541290108417315123981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5007694193405611543415987 7511541290108417315123981)
                ·
                  refine ⟨2816827983790656493171493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7511541290108417315123981 2816827983790656493171493)
                  ·
                    refine ⟨528155246960748092469655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2816827983790656493171493 528155246960748092469655)
                    ·
                      rfl

theorem cell23_3085736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3085736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085736 prefixEnd_3085736 := by exact prefixLift 3085736
  have htrace : WordTrace (prefixWord ++ tailWord_3085736) baseStart_3085736 baseEnd_3085736 := by
    simpa [prefixWord, tailWord_3085736, baseEnd_3085736] using wordTrace_append hprefix tailTrace_3085736
  have hstable : (prefixWord ++ tailWord_3085736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085736).length < 2 ^ (prefixWord ++ tailWord_3085736).sum := by decide
  have hdescent : baseEnd_3085736 < baseStart_3085736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085785 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 5]
def baseStart_3085785 : Nat := 118140960795 + 3085785 * 2 ^ 59
def prefixEnd_3085785 : Nat := 4983230072969 + 3 ^ 40 * 3085785 * 2
def baseEnd_3085785 : Nat := 1584490901434314585696239

theorem tailTrace_3085785 : CollatzResearch.WordTrace tailWord_3085785 prefixEnd_3085785 1584490901434314585696239 := by
  unfold tailWord_3085785
  simp only [CollatzResearch.WordTrace]
  refine ⟨112547825125735429965690809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75031883417156953310460539 112547825125735429965690809)
  ·
    refine ⟨84410868844301572474268107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112547825125735429965690809 84410868844301572474268107)
    ·
      refine ⟨126616303266452358711402161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84410868844301572474268107 126616303266452358711402161)
      ·
        refine ⟨94962227449839269033551621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126616303266452358711402161 94962227449839269033551621)
        ·
          refine ⟨17805417646844862943790929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94962227449839269033551621 17805417646844862943790929)
          ·
            refine ⟨13354063235133647207843197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17805417646844862943790929 13354063235133647207843197)
            ·
              refine ⟨5007773713175117702941199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13354063235133647207843197 5007773713175117702941199)
              ·
                refine ⟨7511660569762676554411799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5007773713175117702941199 7511660569762676554411799)
                ·
                  refine ⟨11267490854644014831617699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511660569762676554411799 11267490854644014831617699)
                  ·
                    refine ⟨16901236281966022247426549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11267490854644014831617699 16901236281966022247426549)
                    ·
                      refine ⟨1584490901434314585696239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16901236281966022247426549 1584490901434314585696239)
                      ·
                        rfl

theorem cell23_3085785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_3085785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085785 prefixEnd_3085785 := by exact prefixLift 3085785
  have htrace : WordTrace (prefixWord ++ tailWord_3085785) baseStart_3085785 baseEnd_3085785 := by
    simpa [prefixWord, tailWord_3085785, baseEnd_3085785] using wordTrace_append hprefix tailTrace_3085785
  have hstable : (prefixWord ++ tailWord_3085785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085785).length < 2 ^ (prefixWord ++ tailWord_3085785).sum := by decide
  have hdescent : baseEnd_3085785 < baseStart_3085785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085818 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_3085818 : Nat := 118140960795 + 3085818 * 2 ^ 59
def prefixEnd_3085818 : Nat := 4983230072969 + 3 ^ 40 * 3085818 * 2
def baseEnd_3085818 : Nat := 528169282098637652194529

theorem tailTrace_3085818 : CollatzResearch.WordTrace tailWord_3085818 prefixEnd_3085818 528169282098637652194529 := by
  unfold tailWord_3085818
  simp only [CollatzResearch.WordTrace]
  refine ⟨28137257183653969150410527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75032685823077251067761405 28137257183653969150410527)
  ·
    refine ⟨42205885775480953725615791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28137257183653969150410527 42205885775480953725615791)
    ·
      refine ⟨63308828663221430588423687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42205885775480953725615791 63308828663221430588423687)
      ·
        refine ⟨94963242994832145882635531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63308828663221430588423687 94963242994832145882635531)
        ·
          refine ⟨142444864492248218823953297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94963242994832145882635531 142444864492248218823953297)
          ·
            refine ⟨106833648369186164117964973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142444864492248218823953297 106833648369186164117964973)
            ·
              refine ⟨40062618138444811544236865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106833648369186164117964973 40062618138444811544236865)
              ·
                refine ⟨30046963603833608658177649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40062618138444811544236865 30046963603833608658177649)
                ·
                  refine ⟨22535222702875206493633237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30046963603833608658177649 22535222702875206493633237)
                  ·
                    refine ⟨528169282098637652194529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22535222702875206493633237 528169282098637652194529)
                    ·
                      rfl

theorem cell23_3085818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_3085818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085818 prefixEnd_3085818 := by exact prefixLift 3085818
  have htrace : WordTrace (prefixWord ++ tailWord_3085818) baseStart_3085818 baseEnd_3085818 := by
    simpa [prefixWord, tailWord_3085818, baseEnd_3085818] using wordTrace_append hprefix tailTrace_3085818
  have hstable : (prefixWord ++ tailWord_3085818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085818).length < 2 ^ (prefixWord ++ tailWord_3085818).sum := by decide
  have hdescent : baseEnd_3085818 < baseStart_3085818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085830 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3085830 : Nat := 118140960795 + 3085830 * 2 ^ 59
def prefixEnd_3085830 : Nat := 4983230072969 + 3 ^ 40 * 3085830 * 2
def baseEnd_3085830 : Nat := 528171336021255636544511

theorem tailTrace_3085830 : CollatzResearch.WordTrace tailWord_3085830 prefixEnd_3085830 528171336021255636544511 := by
  unfold tailWord_3085830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517170825330387582846217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75032977607048268434052629 3517170825330387582846217)
  ·
    refine ⟨2637878118997790687134663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3517170825330387582846217 2637878118997790687134663)
    ·
      refine ⟨3956817178496686030701995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2637878118997790687134663 3956817178496686030701995)
      ·
        refine ⟨5935225767745029046052993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956817178496686030701995 5935225767745029046052993)
        ·
          refine ⟨4451419325808771784539745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5935225767745029046052993 4451419325808771784539745)
          ·
            refine ⟨3338564494356578838404809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4451419325808771784539745 3338564494356578838404809)
            ·
              refine ⟨2503923370767434128803607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3338564494356578838404809 2503923370767434128803607)
              ·
                refine ⟨3755885056151151193205411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503923370767434128803607 3755885056151151193205411)
                ·
                  refine ⟨5633827584226726789808117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755885056151151193205411 5633827584226726789808117)
                  ·
                    refine ⟨528171336021255636544511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5633827584226726789808117 528171336021255636544511)
                    ·
                      rfl

theorem cell23_3085830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3085830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085830 prefixEnd_3085830 := by exact prefixLift 3085830
  have htrace : WordTrace (prefixWord ++ tailWord_3085830) baseStart_3085830 baseEnd_3085830 := by
    simpa [prefixWord, tailWord_3085830, baseEnd_3085830] using wordTrace_append hprefix tailTrace_3085830
  have hstable : (prefixWord ++ tailWord_3085830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085830).length < 2 ^ (prefixWord ++ tailWord_3085830).sum := by decide
  have hdescent : baseEnd_3085830 < baseStart_3085830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085836 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 1, 2, 3]
def baseStart_3085836 : Nat := 118140960795 + 3085836 * 2 ^ 59
def prefixEnd_3085836 : Nat := 4983230072969 + 3 ^ 40 * 3085836 * 2
def baseEnd_3085836 : Nat := 1584517088947693886158505

theorem tailTrace_3085836 : CollatzResearch.WordTrace tailWord_3085836 prefixEnd_3085836 1584517088947693886158505 := by
  unfold tailWord_3085836
  simp only [CollatzResearch.WordTrace]
  refine ⟨56274842624275332837898681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75033123499033777117198241 56274842624275332837898681)
  ·
    refine ⟨42206131968206499628424011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56274842624275332837898681 42206131968206499628424011)
    ·
      refine ⟨63309197952309749442636017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42206131968206499628424011 63309197952309749442636017)
      ·
        refine ⟨47481898464232312081977013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63309197952309749442636017 47481898464232312081977013)
        ·
          refine ⟨4451427981021779257685345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47481898464232312081977013 4451427981021779257685345)
          ·
            refine ⟨3338570985766334443264009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4451427981021779257685345 3338570985766334443264009)
            ·
              refine ⟨2503928239324750832448007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3338570985766334443264009 2503928239324750832448007)
              ·
                refine ⟨3755892358987126248672011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503928239324750832448007 3755892358987126248672011)
                ·
                  refine ⟨5633838538480689373008017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755892358987126248672011 5633838538480689373008017)
                  ·
                    refine ⟨4225378903860517029756013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5633838538480689373008017 4225378903860517029756013)
                    ·
                      refine ⟨1584517088947693886158505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4225378903860517029756013 1584517088947693886158505)
                      ·
                        rfl

theorem cell23_3085836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_3085836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085836 prefixEnd_3085836 := by exact prefixLift 3085836
  have htrace : WordTrace (prefixWord ++ tailWord_3085836) baseStart_3085836 baseEnd_3085836 := by
    simpa [prefixWord, tailWord_3085836, baseEnd_3085836] using wordTrace_append hprefix tailTrace_3085836
  have hstable : (prefixWord ++ tailWord_3085836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085836).length < 2 ^ (prefixWord ++ tailWord_3085836).sum := by decide
  have hdescent : baseEnd_3085836 < baseStart_3085836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085866 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_3085866 : Nat := 118140960795 + 3085866 * 2 ^ 59
def prefixEnd_3085866 : Nat := 4983230072969 + 3 ^ 40 * 3085866 * 2
def baseEnd_3085866 : Nat := 1584532493367328768783367

theorem tailTrace_3085866 : CollatzResearch.WordTrace tailWord_3085866 prefixEnd_3085866 1584532493367328768783367 := by
  unfold tailWord_3085866
  simp only [CollatzResearch.WordTrace]
  refine ⟨28137694859610495199847363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75033852958961320532926301 28137694859610495199847363)
  ·
    refine ⟨42206542289415742799771045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28137694859610495199847363 42206542289415742799771045)
    ·
      refine ⟨7913726679265451774957071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42206542289415742799771045 7913726679265451774957071)
      ·
        refine ⟨11870590018898177662435607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7913726679265451774957071 11870590018898177662435607)
        ·
          refine ⟨17805885028347266493653411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11870590018898177662435607 17805885028347266493653411)
          ·
            refine ⟨26708827542520899740480117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17805885028347266493653411 26708827542520899740480117)
            ·
              refine ⟨2503952582111334350670011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26708827542520899740480117 2503952582111334350670011)
              ·
                refine ⟨3755928873167001526005017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503952582111334350670011 3755928873167001526005017)
                ·
                  refine ⟨2816946654875251144503763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3755928873167001526005017 2816946654875251144503763)
                  ·
                    refine ⟨4225419982312876716755645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2816946654875251144503763 4225419982312876716755645)
                    ·
                      refine ⟨1584532493367328768783367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4225419982312876716755645 1584532493367328768783367)
                      ·
                        rfl

theorem cell23_3085866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_3085866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085866 prefixEnd_3085866 := by exact prefixLift 3085866
  have htrace : WordTrace (prefixWord ++ tailWord_3085866) baseStart_3085866 baseEnd_3085866 := by
    simpa [prefixWord, tailWord_3085866, baseEnd_3085866] using wordTrace_append hprefix tailTrace_3085866
  have hstable : (prefixWord ++ tailWord_3085866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085866).length < 2 ^ (prefixWord ++ tailWord_3085866).sum := by decide
  have hdescent : baseEnd_3085866 < baseStart_3085866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085889 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_3085889 : Nat := 118140960795 + 3085889 * 2 ^ 59
def prefixEnd_3085889 : Nat := 4983230072969 + 3 ^ 40 * 3085889 * 2
def baseEnd_3085889 : Nat := 1584544303422382178795761

theorem tailTrace_3085889 : CollatzResearch.WordTrace tailWord_3085889 prefixEnd_3085889 1584544303422382178795761 := by
  unfold tailWord_3085889
  simp only [CollatzResearch.WordTrace]
  refine ⟨112551618317358655727476721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75034412211572437151651147 112551618317358655727476721)
  ·
    refine ⟨84413713738018991795607541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112551618317358655727476721 84413713738018991795607541)
    ·
      refine ⟨7913785662939280480838207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84413713738018991795607541 7913785662939280480838207)
      ·
        refine ⟨11870678494408920721257311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7913785662939280480838207 11870678494408920721257311)
        ·
          refine ⟨17806017741613381081885967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11870678494408920721257311 17806017741613381081885967)
          ·
            refine ⟨26709026612420071622828951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17806017741613381081885967 26709026612420071622828951)
            ·
              refine ⟨40063539918630107434243427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26709026612420071622828951 40063539918630107434243427)
              ·
                refine ⟨60095309877945161151365141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40063539918630107434243427 60095309877945161151365141)
                ·
                  refine ⟨2816967650528679428970241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60095309877945161151365141 2816967650528679428970241)
                  ·
                    refine ⟨2112725737896509571727681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2816967650528679428970241 2112725737896509571727681)
                    ·
                      refine ⟨1584544303422382178795761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112725737896509571727681 1584544303422382178795761)
                      ·
                        rfl

theorem cell23_3085889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_3085889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085889 prefixEnd_3085889 := by exact prefixLift 3085889
  have htrace : WordTrace (prefixWord ++ tailWord_3085889) baseStart_3085889 baseEnd_3085889 := by
    simpa [prefixWord, tailWord_3085889, baseEnd_3085889] using wordTrace_append hprefix tailTrace_3085889
  have hstable : (prefixWord ++ tailWord_3085889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085889).length < 2 ^ (prefixWord ++ tailWord_3085889).sum := by decide
  have hdescent : baseEnd_3085889 < baseStart_3085889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085917 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3085917 : Nat := 118140960795 + 3085917 * 2 ^ 59
def prefixEnd_3085917 : Nat := 4983230072969 + 3 ^ 40 * 3085917 * 2
def baseEnd_3085917 : Nat := 1584558680880708069245633

theorem tailTrace_3085917 : CollatzResearch.WordTrace tailWord_3085917 prefixEnd_3085917 1584558680880708069245633 := by
  unfold tailWord_3085917
  simp only [CollatzResearch.WordTrace]
  refine ⟨112552639561257216509496005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75035093040838144339664003 112552639561257216509496005)
  ·
    refine ⟨21103619917735728095530501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112552639561257216509496005 21103619917735728095530501)
    ·
      refine ⟨3956928734575449017911969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21103619917735728095530501 3956928734575449017911969)
      ·
        refine ⟨2967696550931586763433977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3956928734575449017911969 2967696550931586763433977)
        ·
          refine ⟨2225772413198690072575483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2967696550931586763433977 2225772413198690072575483)
          ·
            refine ⟨3338658619798035108863225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225772413198690072575483 3338658619798035108863225)
            ·
              refine ⟨2503993964848526331647419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3338658619798035108863225 2503993964848526331647419)
              ·
                refine ⟨3755990947272789497471129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503993964848526331647419 3755990947272789497471129)
                ·
                  refine ⟨2816993210454592123103347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3755990947272789497471129 2816993210454592123103347)
                  ·
                    refine ⟨4225489815681888184655021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2816993210454592123103347 4225489815681888184655021)
                    ·
                      refine ⟨1584558680880708069245633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4225489815681888184655021 1584558680880708069245633)
                      ·
                        rfl

theorem cell23_3085917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3085917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085917 prefixEnd_3085917 := by exact prefixLift 3085917
  have htrace : WordTrace (prefixWord ++ tailWord_3085917) baseStart_3085917 baseEnd_3085917 := by
    simpa [prefixWord, tailWord_3085917, baseEnd_3085917] using wordTrace_append hprefix tailTrace_3085917
  have hstable : (prefixWord ++ tailWord_3085917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085917).length < 2 ^ (prefixWord ++ tailWord_3085917).sum := by decide
  have hdescent : baseEnd_3085917 < baseStart_3085917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3085923 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 2, 2, 2]
def baseStart_3085923 : Nat := 118140960795 + 3085923 * 2 ^ 59
def prefixEnd_3085923 : Nat := 4983230072969 + 3 ^ 40 * 3085923 * 2
def baseEnd_3085923 : Nat := 1584561761764635045770605

theorem tailTrace_3085923 : CollatzResearch.WordTrace tailWord_3085923 prefixEnd_3085923 1584561761764635045770605 := by
  unfold tailWord_3085923
  simp only [CollatzResearch.WordTrace]
  refine ⟨112552858399235479534214423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75035238932823653022809615 112552858399235479534214423)
  ·
    refine ⟨168829287598853219301321635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112552858399235479534214423 168829287598853219301321635)
    ·
      refine ⟨253243931398279828951982453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168829287598853219301321635 253243931398279828951982453)
      ·
        refine ⟨23741618568588733964248355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253243931398279828951982453 23741618568588733964248355)
        ·
          refine ⟨35612427852883100946372533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23741618568588733964248355 35612427852883100946372533)
          ·
            refine ⟨3338665111207790713722425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35612427852883100946372533 3338665111207790713722425)
            ·
              refine ⟨2503998833405843035291819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3338665111207790713722425 2503998833405843035291819)
              ·
                refine ⟨3755998250108764552937729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503998833405843035291819 3755998250108764552937729)
                ·
                  refine ⟨2816998687581573414703297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3755998250108764552937729 2816998687581573414703297)
                  ·
                    refine ⟨2112749015686180061027473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2816998687581573414703297 2112749015686180061027473)
                    ·
                      refine ⟨1584561761764635045770605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112749015686180061027473 1584561761764635045770605)
                      ·
                        rfl

theorem cell23_3085923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_3085923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3085923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3085923 prefixEnd_3085923 := by exact prefixLift 3085923
  have htrace : WordTrace (prefixWord ++ tailWord_3085923) baseStart_3085923 baseEnd_3085923 := by
    simpa [prefixWord, tailWord_3085923, baseEnd_3085923] using wordTrace_append hprefix tailTrace_3085923
  have hstable : (prefixWord ++ tailWord_3085923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3085923).length < 2 ^ (prefixWord ++ tailWord_3085923).sum := by decide
  have hdescent : baseEnd_3085923 < baseStart_3085923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3085923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086036 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 6]
def baseStart_3086036 : Nat := 118140960795 + 3086036 * 2 ^ 59
def prefixEnd_3086036 : Nat := 4983230072969 + 3 ^ 40 * 3086036 * 2
def baseEnd_3086036 : Nat := 176068865008732567073065

theorem tailTrace_3086036 : CollatzResearch.WordTrace tailWord_3086036 prefixEnd_3086036 176068865008732567073065 := by
  unfold tailWord_3086036
  simp only [CollatzResearch.WordTrace]
  refine ⟨56278489923913049916538981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75037986565217399888718641 56278489923913049916538981)
  ·
    refine ⟨10552216860733696859351059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56278489923913049916538981 10552216860733696859351059)
    ·
      refine ⟨15828325291100545289026589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10552216860733696859351059 15828325291100545289026589)
      ·
        refine ⟨5935621984162704483384971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15828325291100545289026589 5935621984162704483384971)
        ·
          refine ⟨8903432976244056725077457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5935621984162704483384971 8903432976244056725077457)
          ·
            refine ⟨6677574732183042543808093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8903432976244056725077457 6677574732183042543808093)
            ·
              refine ⟨2504090524568640953928035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6677574732183042543808093 2504090524568640953928035)
              ·
                refine ⟨3756135786852961430892053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504090524568640953928035 3756135786852961430892053)
                ·
                  refine ⟨176068865008732567073065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3756135786852961430892053 176068865008732567073065)
                  ·
                    rfl

theorem cell23_3086036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_3086036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086036 prefixEnd_3086036 := by exact prefixLift 3086036
  have htrace : WordTrace (prefixWord ++ tailWord_3086036) baseStart_3086036 baseEnd_3086036 := by
    simpa [prefixWord, tailWord_3086036, baseEnd_3086036] using wordTrace_append hprefix tailTrace_3086036
  have hstable : (prefixWord ++ tailWord_3086036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086036).length < 2 ^ (prefixWord ++ tailWord_3086036).sum := by decide
  have hdescent : baseEnd_3086036 < baseStart_3086036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086062 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3086062 : Nat := 118140960795 + 3086062 * 2 ^ 59
def prefixEnd_3086062 : Nat := 4983230072969 + 3 ^ 40 * 3086062 * 2
def baseEnd_3086062 : Nat := 528211045191870000644155

theorem tailTrace_3086062 : CollatzResearch.WordTrace tailWord_3086062 prefixEnd_3086062 528211045191870000644155 := by
  unfold tailWord_3086062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14069741018216488284190555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75038618763821270849016293 14069741018216488284190555)
  ·
    refine ⟨21104611527324732426285833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14069741018216488284190555 21104611527324732426285833)
    ·
      refine ⟨15828458645493549319714375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21104611527324732426285833 15828458645493549319714375)
      ·
        refine ⟨23742687968240323979571563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15828458645493549319714375 23742687968240323979571563)
        ·
          refine ⟨35614031952360485969357345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23742687968240323979571563 35614031952360485969357345)
          ·
            refine ⟨26710523964270364477018009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35614031952360485969357345 26710523964270364477018009)
            ·
              refine ⟨20032892973202773357763507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26710523964270364477018009 20032892973202773357763507)
              ·
                refine ⟨30049339459804160036645261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20032892973202773357763507 30049339459804160036645261)
                ·
                  refine ⟨11268502297426560013741973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30049339459804160036645261 11268502297426560013741973)
                  ·
                    refine ⟨528211045191870000644155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11268502297426560013741973 528211045191870000644155)
                    ·
                      rfl

theorem cell23_3086062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3086062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086062 prefixEnd_3086062 := by exact prefixLift 3086062
  have htrace : WordTrace (prefixWord ++ tailWord_3086062) baseStart_3086062 baseEnd_3086062 := by
    simpa [prefixWord, tailWord_3086062, baseEnd_3086062] using wordTrace_append hprefix tailTrace_3086062
  have hstable : (prefixWord ++ tailWord_3086062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086062).length < 2 ^ (prefixWord ++ tailWord_3086062).sum := by decide
  have hdescent : baseEnd_3086062 < baseStart_3086062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086106 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3]
def baseStart_3086106 : Nat := 118140960795 + 3086106 * 2 ^ 59
def prefixEnd_3086106 : Nat := 4983230072969 + 3 ^ 40 * 3086106 * 2
def baseEnd_3086106 : Nat := 1584655728724407829782263

theorem tailTrace_3086106 : CollatzResearch.WordTrace tailWord_3086106 prefixEnd_3086106 1584655728724407829782263 := by
  unfold tailWord_3086106
  simp only [CollatzResearch.WordTrace]
  refine ⟨28139883239393125447031543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75039688638381667858750781 28139883239393125447031543)
  ·
    refine ⟨42209824859089688170547315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28139883239393125447031543 42209824859089688170547315)
    ·
      refine ⟨63314737288634532255820973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42209824859089688170547315 63314737288634532255820973)
      ·
        refine ⟨23743026483237949595932865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63314737288634532255820973 23743026483237949595932865)
        ·
          refine ⟨17807269862428462196949649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23743026483237949595932865 17807269862428462196949649)
          ·
            refine ⟨13355452396821346647712237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17807269862428462196949649 13355452396821346647712237)
            ·
              refine ⟨5008294648808004992892089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13355452396821346647712237 5008294648808004992892089)
              ·
                refine ⟨3756220986606003744669067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5008294648808004992892089 3756220986606003744669067)
                ·
                  refine ⟨5634331479909005617003601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3756220986606003744669067 5634331479909005617003601)
                  ·
                    refine ⟨4225748609931754212752701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5634331479909005617003601 4225748609931754212752701)
                    ·
                      refine ⟨1584655728724407829782263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4225748609931754212752701 1584655728724407829782263)
                      ·
                        rfl

theorem cell23_3086106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_3086106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086106 prefixEnd_3086106 := by exact prefixLift 3086106
  have htrace : WordTrace (prefixWord ++ tailWord_3086106) baseStart_3086106 baseEnd_3086106 := by
    simpa [prefixWord, tailWord_3086106, baseEnd_3086106] using wordTrace_append hprefix tailTrace_3086106
  have hstable : (prefixWord ++ tailWord_3086106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086106).length < 2 ^ (prefixWord ++ tailWord_3086106).sum := by decide
  have hdescent : baseEnd_3086106 < baseStart_3086106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086136 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 2, 1, 3]
def baseStart_3086136 : Nat := 118140960795 + 3086136 * 2 ^ 59
def prefixEnd_3086136 : Nat := 4983230072969 + 3 ^ 40 * 3086136 * 2
def baseEnd_3086136 : Nat := 1584671133144042712407125

theorem tailTrace_3086136 : CollatzResearch.WordTrace tailWord_3086136 prefixEnd_3086136 1584671133144042712407125 := by
  unfold tailWord_3086136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56280313573731908455859131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75040418098309211274478841 56280313573731908455859131)
  ·
    refine ⟨84420470360597862683788697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56280313573731908455859131 84420470360597862683788697)
    ·
      refine ⟨63315352770448397012841523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84420470360597862683788697 63315352770448397012841523)
      ·
        refine ⟨94973029155672595519262285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63315352770448397012841523 94973029155672595519262285)
        ·
          refine ⟨35614885933377223319723357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94973029155672595519262285 35614885933377223319723357)
          ·
            refine ⟨13355582225016458744896259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35614885933377223319723357 13355582225016458744896259)
            ·
              refine ⟨20033373337524688117344389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13355582225016458744896259 20033373337524688117344389)
              ·
                refine ⟨3756257500785879022002073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20033373337524688117344389 3756257500785879022002073)
                ·
                  refine ⟨2817193125589409266501555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3756257500785879022002073 2817193125589409266501555)
                  ·
                    refine ⟨4225789688384113899752333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2817193125589409266501555 4225789688384113899752333)
                    ·
                      refine ⟨1584671133144042712407125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4225789688384113899752333 1584671133144042712407125)
                      ·
                        rfl

theorem cell23_3086136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_3086136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086136 prefixEnd_3086136 := by exact prefixLift 3086136
  have htrace : WordTrace (prefixWord ++ tailWord_3086136) baseStart_3086136 baseEnd_3086136 := by
    simpa [prefixWord, tailWord_3086136, baseEnd_3086136] using wordTrace_append hprefix tailTrace_3086136
  have hstable : (prefixWord ++ tailWord_3086136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086136).length < 2 ^ (prefixWord ++ tailWord_3086136).sum := by decide
  have hdescent : baseEnd_3086136 < baseStart_3086136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086137 : List Nat := [1, 2, 1, 7, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3086137 : Nat := 118140960795 + 3086137 * 2 ^ 59
def prefixEnd_3086137 : Nat := 4983230072969 + 3 ^ 40 * 3086137 * 2
def baseEnd_3086137 : Nat := 1584671646624697208494621

theorem tailTrace_3086137 : CollatzResearch.WordTrace tailWord_3086137 prefixEnd_3086137 1584671646624697208494621 := by
  unfold tailWord_3086137
  simp only [CollatzResearch.WordTrace]
  refine ⟨112560663620460194082504665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75040442413640129388336443 112560663620460194082504665)
  ·
    refine ⟨84420497715345145561878499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112560663620460194082504665 84420497715345145561878499)
    ·
      refine ⟨126630746573017718342817749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84420497715345145561878499 126630746573017718342817749)
      ·
        refine ⟨2967908122805102773659791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 126630746573017718342817749 2967908122805102773659791)
        ·
          refine ⟨4451862184207654160489687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967908122805102773659791 4451862184207654160489687)
          ·
            refine ⟨6677793276311481240734531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451862184207654160489687 6677793276311481240734531)
            ·
              refine ⟨10016689914467221861101797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6677793276311481240734531 10016689914467221861101797)
              ·
                refine ⟨1878129358962604098956587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10016689914467221861101797 1878129358962604098956587)
                ·
                  refine ⟨2817194038443906148434881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878129358962604098956587 2817194038443906148434881)
                  ·
                    refine ⟨2112895528832929611326161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2817194038443906148434881 2112895528832929611326161)
                    ·
                      refine ⟨1584671646624697208494621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112895528832929611326161 1584671646624697208494621)
                      ·
                        rfl

theorem cell23_3086137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3086137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086137 prefixEnd_3086137 := by exact prefixLift 3086137
  have htrace : WordTrace (prefixWord ++ tailWord_3086137) baseStart_3086137 baseEnd_3086137 := by
    simpa [prefixWord, tailWord_3086137, baseEnd_3086137] using wordTrace_append hprefix tailTrace_3086137
  have hstable : (prefixWord ++ tailWord_3086137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086137).length < 2 ^ (prefixWord ++ tailWord_3086137).sum := by decide
  have hdescent : baseEnd_3086137 < baseStart_3086137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086152 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 1, 8]
def baseStart_3086152 : Nat := 118140960795 + 3086152 * 2 ^ 59
def prefixEnd_3086152 : Nat := 4983230072969 + 3 ^ 40 * 3086152 * 2
def baseEnd_3086152 : Nat := 528226449611504883269017

theorem tailTrace_3086152 : CollatzResearch.WordTrace tailWord_3086152 prefixEnd_3086152 528226449611504883269017 := by
  unfold tailWord_3086152
  simp only [CollatzResearch.WordTrace]
  refine ⟨56280605357702925822150355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75040807143603901096200473 56280605357702925822150355)
  ·
    refine ⟨84420908036554388733225533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56280605357702925822150355 84420908036554388733225533)
    ·
      refine ⟨31657840513707895774959575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84420908036554388733225533 31657840513707895774959575)
      ·
        refine ⟨47486760770561843662439363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31657840513707895774959575 47486760770561843662439363)
        ·
          refine ⟨71230141155842765493659045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47486760770561843662439363 71230141155842765493659045)
          ·
            refine ⟨13355651466720518530061071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71230141155842765493659045 13355651466720518530061071)
            ·
              refine ⟨20033477200080777795091607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13355651466720518530061071 20033477200080777795091607)
              ·
                refine ⟨30050215800121166692637411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20033477200080777795091607 30050215800121166692637411)
                ·
                  refine ⟨45075323700181750038956117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30050215800121166692637411 45075323700181750038956117)
                  ·
                    refine ⟨528226449611504883269017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45075323700181750038956117 528226449611504883269017)
                    ·
                      rfl

theorem cell23_3086152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_3086152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086152 prefixEnd_3086152 := by exact prefixLift 3086152
  have htrace : WordTrace (prefixWord ++ tailWord_3086152) baseStart_3086152 baseEnd_3086152 := by
    simpa [prefixWord, tailWord_3086152, baseEnd_3086152] using wordTrace_append hprefix tailTrace_3086152
  have hstable : (prefixWord ++ tailWord_3086152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086152).length < 2 ^ (prefixWord ++ tailWord_3086152).sum := by decide
  have hdescent : baseEnd_3086152 < baseStart_3086152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086176 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 1, 4, 2]
def baseStart_3086176 : Nat := 118140960795 + 3086176 * 2 ^ 59
def prefixEnd_3086176 : Nat := 4983230072969 + 3 ^ 40 * 3086176 * 2
def baseEnd_3086176 : Nat := 1584691672370222555906941

theorem tailTrace_3086176 : CollatzResearch.WordTrace tailWord_3086176 prefixEnd_3086176 1584691672370222555906941 := by
  unfold tailWord_3086176
  simp only [CollatzResearch.WordTrace]
  refine ⟨56281043033659451871587191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75041390711545935828782921 56281043033659451871587191)
  ·
    refine ⟨84421564550489177807380787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56281043033659451871587191 84421564550489177807380787)
    ·
      refine ⟨126632346825733766711071181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84421564550489177807380787 126632346825733766711071181)
      ·
        refine ⟨47487130059650162516651693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126632346825733766711071181 47487130059650162516651693)
        ·
          refine ⟨17807673772368810943744385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47487130059650162516651693 17807673772368810943744385)
          ·
            refine ⟨13355755329276608207808289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17807673772368810943744385 13355755329276608207808289)
            ·
              refine ⟨10016816496957456155856217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13355755329276608207808289 10016816496957456155856217)
              ·
                refine ⟨7512612372718092116892163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10016816496957456155856217 7512612372718092116892163)
                ·
                  refine ⟨11268918559077138175338245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7512612372718092116892163 11268918559077138175338245)
                  ·
                    refine ⟨2112922229826963407875921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11268918559077138175338245 2112922229826963407875921)
                    ·
                      refine ⟨1584691672370222555906941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2112922229826963407875921 1584691672370222555906941)
                      ·
                        rfl

theorem cell23_3086176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_3086176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086176 prefixEnd_3086176 := by exact prefixLift 3086176
  have htrace : WordTrace (prefixWord ++ tailWord_3086176) baseStart_3086176 baseEnd_3086176 := by
    simpa [prefixWord, tailWord_3086176, baseEnd_3086176] using wordTrace_append hprefix tailTrace_3086176
  have hstable : (prefixWord ++ tailWord_3086176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086176).length < 2 ^ (prefixWord ++ tailWord_3086176).sum := by decide
  have hdescent : baseEnd_3086176 < baseStart_3086176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086189 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3086189 : Nat := 118140960795 + 3086189 * 2 ^ 59
def prefixEnd_3086189 : Nat := 4983230072969 + 3 ^ 40 * 3086189 * 2
def baseEnd_3086189 : Nat := 1584698347618731005044381

theorem tailTrace_3086189 : CollatzResearch.WordTrace tailWord_3086189 prefixEnd_3086189 1584698347618731005044381 := by
  unfold tailWord_3086189
  simp only [CollatzResearch.WordTrace]
  refine ⟨112562560216271806963397621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75041706810847871308931747 112562560216271806963397621)
  ·
    refine ⟨10552740020275481902818527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112562560216271806963397621 10552740020275481902818527)
    ·
      refine ⟨15829110030413222854227791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10552740020275481902818527 15829110030413222854227791)
      ·
        refine ⟨23743665045619834281341687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15829110030413222854227791 23743665045619834281341687)
        ·
          refine ⟨35615497568429751422012531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23743665045619834281341687 35615497568429751422012531)
          ·
            refine ⟨53423246352644627133018797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35615497568429751422012531 53423246352644627133018797)
            ·
              refine ⟨20033717382241735174882049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53423246352644627133018797 20033717382241735174882049)
              ·
                refine ⟨15025288036681301381161537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20033717382241735174882049 15025288036681301381161537)
                ·
                  refine ⟨11268966027510976035871153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15025288036681301381161537 11268966027510976035871153)
                  ·
                    refine ⟨8451724520633232026903365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11268966027510976035871153 8451724520633232026903365)
                    ·
                      refine ⟨1584698347618731005044381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8451724520633232026903365 1584698347618731005044381)
                      ·
                        rfl

theorem cell23_3086189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3086189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086189 prefixEnd_3086189 := by exact prefixLift 3086189
  have htrace : WordTrace (prefixWord ++ tailWord_3086189) baseStart_3086189 baseEnd_3086189 := by
    simpa [prefixWord, tailWord_3086189, baseEnd_3086189] using wordTrace_append hprefix tailTrace_3086189
  have hstable : (prefixWord ++ tailWord_3086189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086189).length < 2 ^ (prefixWord ++ tailWord_3086189).sum := by decide
  have hdescent : baseEnd_3086189 < baseStart_3086189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086229 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_3086229 : Nat := 118140960795 + 3086229 * 2 ^ 59
def prefixEnd_3086229 : Nat := 4983230072969 + 3 ^ 40 * 3086229 * 2
def baseEnd_3086229 : Nat := 528239628948303616181399

theorem tailTrace_3086229 : CollatzResearch.WordTrace tailWord_3086229 prefixEnd_3086229 528239628948303616181399 := by
  unfold tailWord_3086229
  simp only [CollatzResearch.WordTrace]
  refine ⟨112564019136126893794853741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75042679424084595863235827 112564019136126893794853741)
  ·
    refine ⟨42211507176047585173070153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112564019136126893794853741 42211507176047585173070153)
    ·
      refine ⟨31658630382035688879802615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42211507176047585173070153 31658630382035688879802615)
      ·
        refine ⟨47487945573053533319703923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31658630382035688879802615 47487945573053533319703923)
        ·
          refine ⟨71231918359580299979555885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47487945573053533319703923 71231918359580299979555885)
          ·
            refine ⟨26711969384842612492333457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71231918359580299979555885 26711969384842612492333457)
            ·
              refine ⟨20033977038631959369250093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26711969384842612492333457 20033977038631959369250093)
              ·
                refine ⟨7512741389486984763468785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20033977038631959369250093 7512741389486984763468785)
                ·
                  refine ⟨5634556042115238572601589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7512741389486984763468785 5634556042115238572601589)
                  ·
                    refine ⟨528239628948303616181399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5634556042115238572601589 528239628948303616181399)
                    ·
                      rfl

theorem cell23_3086229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_3086229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086229 prefixEnd_3086229 := by exact prefixLift 3086229
  have htrace : WordTrace (prefixWord ++ tailWord_3086229) baseStart_3086229 baseEnd_3086229 := by
    simpa [prefixWord, tailWord_3086229, baseEnd_3086229] using wordTrace_append hprefix tailTrace_3086229
  have hstable : (prefixWord ++ tailWord_3086229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086229).length < 2 ^ (prefixWord ++ tailWord_3086229).sum := by decide
  have hdescent : baseEnd_3086229 < baseStart_3086229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086230 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3086230 : Nat := 118140960795 + 3086230 * 2 ^ 59
def prefixEnd_3086230 : Nat := 4983230072969 + 3 ^ 40 * 3086230 * 2
def baseEnd_3086230 : Nat := 1584719400325565344631693

theorem tailTrace_3086230 : CollatzResearch.WordTrace tailWord_3086230 prefixEnd_3086230 1584719400325565344631693 := by
  unfold tailWord_3086230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7035253475570204435352509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75042703739415513977093429 7035253475570204435352509)
  ·
    refine ⟨2638220053338826663257191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7035253475570204435352509 2638220053338826663257191)
    ·
      refine ⟨3957330080008239994885787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2638220053338826663257191 3957330080008239994885787)
      ·
        refine ⟨5935995120012359992328681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957330080008239994885787 5935995120012359992328681)
        ·
          refine ⟨4451996340009269994246511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5935995120012359992328681 4451996340009269994246511)
          ·
            refine ⟨6677994510013904991369767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451996340009269994246511 6677994510013904991369767)
            ·
              refine ⟨10016991765020857487054651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6677994510013904991369767 10016991765020857487054651)
              ·
                refine ⟨15025487647531286230581977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10016991765020857487054651 15025487647531286230581977)
                ·
                  refine ⟨11269115735648464672936483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15025487647531286230581977 11269115735648464672936483)
                  ·
                    refine ⟨16903673603472697009404725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11269115735648464672936483 16903673603472697009404725)
                    ·
                      refine ⟨1584719400325565344631693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16903673603472697009404725 1584719400325565344631693)
                      ·
                        rfl

theorem cell23_3086230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3086230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086230 prefixEnd_3086230 := by exact prefixLift 3086230
  have htrace : WordTrace (prefixWord ++ tailWord_3086230) baseStart_3086230 baseEnd_3086230 := by
    simpa [prefixWord, tailWord_3086230, baseEnd_3086230] using wordTrace_append hprefix tailTrace_3086230
  have hstable : (prefixWord ++ tailWord_3086230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086230).length < 2 ^ (prefixWord ++ tailWord_3086230).sum := by decide
  have hdescent : baseEnd_3086230 < baseStart_3086230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086316 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 3]
def baseStart_3086316 : Nat := 118140960795 + 3086316 * 2 ^ 59
def prefixEnd_3086316 : Nat := 4983230072969 + 3 ^ 40 * 3086316 * 2
def baseEnd_3086316 : Nat := 1584763559661852008156297

theorem tailTrace_3086316 : CollatzResearch.WordTrace tailWord_3086316 prefixEnd_3086316 1584763559661852008156297 := by
  unfold tailWord_3086316
  simp only [CollatzResearch.WordTrace]
  refine ⟨56283596143405853826635401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75044794857874471768847201 56283596143405853826635401)
  ·
    refine ⟨42212697107554390369976551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56283596143405853826635401 42212697107554390369976551)
    ·
      refine ⟨63319045661331585554964827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42212697107554390369976551 63319045661331585554964827)
      ·
        refine ⟨94978568491997378332447241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63319045661331585554964827 94978568491997378332447241)
        ·
          refine ⟨71233926368998033749335431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94978568491997378332447241 71233926368998033749335431)
          ·
            refine ⟨106850889553497050624003147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71233926368998033749335431 106850889553497050624003147)
            ·
              refine ⟨160276334330245575936004721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106850889553497050624003147 160276334330245575936004721)
              ·
                refine ⟨120207250747684181952003541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160276334330245575936004721 120207250747684181952003541)
                ·
                  refine ⟨2817357439398848014500083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 120207250747684181952003541 2817357439398848014500083)
                  ·
                    refine ⟨4226036159098272021750125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2817357439398848014500083 4226036159098272021750125)
                    ·
                      refine ⟨1584763559661852008156297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4226036159098272021750125 1584763559661852008156297)
                      ·
                        rfl

theorem cell23_3086316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_3086316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086316 prefixEnd_3086316 := by exact prefixLift 3086316
  have htrace : WordTrace (prefixWord ++ tailWord_3086316) baseStart_3086316 baseEnd_3086316 := by
    simpa [prefixWord, tailWord_3086316, baseEnd_3086316] using wordTrace_append hprefix tailTrace_3086316
  have hstable : (prefixWord ++ tailWord_3086316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086316).length < 2 ^ (prefixWord ++ tailWord_3086316).sum := by decide
  have hdescent : baseEnd_3086316 < baseStart_3086316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086319 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 5, 5]
def baseStart_3086319 : Nat := 118140960795 + 3086319 * 2 ^ 59
def prefixEnd_3086319 : Nat := 4983230072969 + 3 ^ 40 * 3086319 * 2
def baseEnd_3086319 : Nat := 528255033367938498806261

theorem tailTrace_3086319 : CollatzResearch.WordTrace tailWord_3086319 prefixEnd_3086319 528255033367938498806261 := by
  unfold tailWord_3086319
  simp only [CollatzResearch.WordTrace]
  refine ⟨112567301705800839165630011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75044867803867226110420007 112567301705800839165630011)
  ·
    refine ⟨168850952558701258748445017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112567301705800839165630011 168850952558701258748445017)
    ·
      refine ⟨126638214419025944061333763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168850952558701258748445017 126638214419025944061333763)
      ·
        refine ⟨189957321628538916092000645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126638214419025944061333763 189957321628538916092000645)
        ·
          refine ⟨35616997805351046767250121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189957321628538916092000645 35616997805351046767250121)
          ·
            refine ⟨26712748354013285075437591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35616997805351046767250121 26712748354013285075437591)
            ·
              refine ⟨40069122531019927613156387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26712748354013285075437591 40069122531019927613156387)
              ·
                refine ⟨60103683796529891419734581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40069122531019927613156387 60103683796529891419734581)
                ·
                  refine ⟨5634720355924677320600117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60103683796529891419734581 5634720355924677320600117)
                  ·
                    refine ⟨528255033367938498806261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5634720355924677320600117 528255033367938498806261)
                    ·
                      rfl

theorem cell23_3086319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_3086319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086319 prefixEnd_3086319 := by exact prefixLift 3086319
  have htrace : WordTrace (prefixWord ++ tailWord_3086319) baseStart_3086319 baseEnd_3086319 := by
    simpa [prefixWord, tailWord_3086319, baseEnd_3086319] using wordTrace_append hprefix tailTrace_3086319
  have hstable : (prefixWord ++ tailWord_3086319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086319).length < 2 ^ (prefixWord ++ tailWord_3086319).sum := by decide
  have hdescent : baseEnd_3086319 < baseStart_3086319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086343 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_3086343 : Nat := 118140960795 + 3086343 * 2 ^ 59
def prefixEnd_3086343 : Nat := 4983230072969 + 3 ^ 40 * 3086343 * 2
def baseEnd_3086343 : Nat := 1584777423639523402518673

theorem tailTrace_3086343 : CollatzResearch.WordTrace tailWord_3086343 prefixEnd_3086343 1584777423639523402518673 := by
  unfold tailWord_3086343
  simp only [CollatzResearch.WordTrace]
  refine ⟨112568177057713891264503683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75045451371809260843002455 112568177057713891264503683)
  ·
    refine ⟨168852265586570836896755525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112568177057713891264503683 168852265586570836896755525)
    ·
      refine ⟨31659799797482031918141661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168852265586570836896755525 31659799797482031918141661)
      ·
        refine ⟨11872424924055761969303123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31659799797482031918141661 11872424924055761969303123)
        ·
          refine ⟨17808637386083642953954685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11872424924055761969303123 17808637386083642953954685)
          ·
            refine ⟨6678239019781366107733007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17808637386083642953954685 6678239019781366107733007)
            ·
              refine ⟨10017358529672049161599511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678239019781366107733007 10017358529672049161599511)
              ·
                refine ⟨15026037794508073742399267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10017358529672049161599511 15026037794508073742399267)
                ·
                  refine ⟨22539056691762110613598901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15026037794508073742399267 22539056691762110613598901)
                  ·
                    refine ⟨2113036564852697870024897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22539056691762110613598901 2113036564852697870024897)
                    ·
                      refine ⟨1584777423639523402518673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113036564852697870024897 1584777423639523402518673)
                      ·
                        rfl

theorem cell23_3086343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_3086343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086343 prefixEnd_3086343 := by exact prefixLift 3086343
  have htrace : WordTrace (prefixWord ++ tailWord_3086343) baseStart_3086343 baseEnd_3086343 := by
    simpa [prefixWord, tailWord_3086343, baseEnd_3086343] using wordTrace_append hprefix tailTrace_3086343
  have hstable : (prefixWord ++ tailWord_3086343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086343).length < 2 ^ (prefixWord ++ tailWord_3086343).sum := by decide
  have hdescent : baseEnd_3086343 < baseStart_3086343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086386 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3086386 : Nat := 118140960795 + 3086386 * 2 ^ 59
def prefixEnd_3086386 : Nat := 4983230072969 + 3 ^ 40 * 3086386 * 2
def baseEnd_3086386 : Nat := 1584799503307666734280975

theorem tailTrace_3086386 : CollatzResearch.WordTrace tailWord_3086386 prefixEnd_3086386 1584799503307666734280975 := by
  unfold tailWord_3086386
  simp only [CollatzResearch.WordTrace]
  refine ⟨28142436349139527402079753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75046496931038739738879341 28142436349139527402079753)
  ·
    refine ⟨21106827261854645551559815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28142436349139527402079753 21106827261854645551559815)
    ·
      refine ⟨31660240892781968327339723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21106827261854645551559815 31660240892781968327339723)
      ·
        refine ⟨47490361339172952491009585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31660240892781968327339723 47490361339172952491009585)
        ·
          refine ⟨35617771004379714368257189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47490361339172952491009585 35617771004379714368257189)
          ·
            refine ⟨6678332063321196444048223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35617771004379714368257189 6678332063321196444048223)
            ·
              refine ⟨10017498094981794666072335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678332063321196444048223 10017498094981794666072335)
              ·
                refine ⟨15026247142472691999108503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10017498094981794666072335 15026247142472691999108503)
                ·
                  refine ⟨22539370713709037998662755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15026247142472691999108503 22539370713709037998662755)
                  ·
                    refine ⟨33809056070563556997994133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22539370713709037998662755 33809056070563556997994133)
                    ·
                      refine ⟨1584799503307666734280975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33809056070563556997994133 1584799503307666734280975)
                      ·
                        rfl

theorem cell23_3086386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3086386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086386 prefixEnd_3086386 := by exact prefixLift 3086386
  have htrace : WordTrace (prefixWord ++ tailWord_3086386) baseStart_3086386 baseEnd_3086386 := by
    simpa [prefixWord, tailWord_3086386, baseEnd_3086386] using wordTrace_append hprefix tailTrace_3086386
  have hstable : (prefixWord ++ tailWord_3086386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086386).length < 2 ^ (prefixWord ++ tailWord_3086386).sum := by decide
  have hdescent : baseEnd_3086386 < baseStart_3086386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086390 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3086390 : Nat := 118140960795 + 3086390 * 2 ^ 59
def prefixEnd_3086390 : Nat := 4983230072969 + 3 ^ 40 * 3086390 * 2
def baseEnd_3086390 : Nat := 1584801557230284718630957

theorem tailTrace_3086390 : CollatzResearch.WordTrace tailWord_3086390 prefixEnd_3086390 1584801557230284718630957 := by
  unfold tailWord_3086390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7035618205533976143216539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75046594192362412194309749 7035618205533976143216539)
  ·
    refine ⟨10553427308300964214824809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7035618205533976143216539 10553427308300964214824809)
    ·
      refine ⟨7915070481225723161118607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10553427308300964214824809 7915070481225723161118607)
      ·
        refine ⟨11872605721838584741677911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915070481225723161118607 11872605721838584741677911)
        ·
          refine ⟨17808908582757877112516867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11872605721838584741677911 17808908582757877112516867)
          ·
            refine ⟨26713362874136815668775301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17808908582757877112516867 26713362874136815668775301)
            ·
              refine ⟨5008755538900652937895369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26713362874136815668775301 5008755538900652937895369)
              ·
                refine ⟨3756566654175489703421527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5008755538900652937895369 3756566654175489703421527)
                ·
                  refine ⟨5634849981263234555132291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3756566654175489703421527 5634849981263234555132291)
                  ·
                    refine ⟨8452274971894851832698437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5634849981263234555132291 8452274971894851832698437)
                    ·
                      refine ⟨1584801557230284718630957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8452274971894851832698437 1584801557230284718630957)
                      ·
                        rfl

theorem cell23_3086390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3086390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086390 prefixEnd_3086390 := by exact prefixLift 3086390
  have htrace : WordTrace (prefixWord ++ tailWord_3086390) baseStart_3086390 baseEnd_3086390 := by
    simpa [prefixWord, tailWord_3086390, baseEnd_3086390] using wordTrace_append hprefix tailTrace_3086390
  have hstable : (prefixWord ++ tailWord_3086390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086390).length < 2 ^ (prefixWord ++ tailWord_3086390).sum := by decide
  have hdescent : baseEnd_3086390 < baseStart_3086390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086419 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 5]
def baseStart_3086419 : Nat := 118140960795 + 3086419 * 2 ^ 59
def prefixEnd_3086419 : Nat := 4983230072969 + 3 ^ 40 * 3086419 * 2
def baseEnd_3086419 : Nat := 1584816448169265105168323

theorem tailTrace_3086419 : CollatzResearch.WordTrace tailWord_3086419 prefixEnd_3086419 1584816448169265105168323 := by
  unfold tailWord_3086419
  simp only [CollatzResearch.WordTrace]
  refine ⟨112570949005438556244270311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75047299336959037496180207 112570949005438556244270311)
  ·
    refine ⟨168856423508157834366405467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112570949005438556244270311 168856423508157834366405467)
    ·
      refine ⟨253284635262236751549608201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168856423508157834366405467 253284635262236751549608201)
      ·
        refine ⟨189963476446677563662206151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253284635262236751549608201 189963476446677563662206151)
        ·
          refine ⟨284945214670016345493309227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189963476446677563662206151 284945214670016345493309227)
          ·
            refine ⟨427417822005024518239963841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284945214670016345493309227 427417822005024518239963841)
            ·
              refine ⟨320563366503768388679972881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427417822005024518239963841 320563366503768388679972881)
              ·
                refine ⟨240422524877826291509979661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320563366503768388679972881 240422524877826291509979661)
                ·
                  refine ⟨90158446829184859316242373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240422524877826291509979661 90158446829184859316242373)
                  ·
                    refine ⟨16904708780472161121795445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90158446829184859316242373 16904708780472161121795445)
                    ·
                      refine ⟨1584816448169265105168323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16904708780472161121795445 1584816448169265105168323)
                      ·
                        rfl

theorem cell23_3086419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_3086419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086419 prefixEnd_3086419 := by exact prefixLift 3086419
  have htrace : WordTrace (prefixWord ++ tailWord_3086419) baseStart_3086419 baseEnd_3086419 := by
    simpa [prefixWord, tailWord_3086419, baseEnd_3086419] using wordTrace_append hprefix tailTrace_3086419
  have hstable : (prefixWord ++ tailWord_3086419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086419).length < 2 ^ (prefixWord ++ tailWord_3086419).sum := by decide
  have hdescent : baseEnd_3086419 < baseStart_3086419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086423 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 3]
def baseStart_3086423 : Nat := 118140960795 + 3086423 * 2 ^ 59
def prefixEnd_3086423 : Nat := 4983230072969 + 3 ^ 40 * 3086423 * 2
def baseEnd_3086423 : Nat := 1584818502091883089518305

theorem tailTrace_3086423 : CollatzResearch.WordTrace tailWord_3086423 prefixEnd_3086423 1584818502091883089518305 := by
  unfold tailWord_3086423
  simp only [CollatzResearch.WordTrace]
  refine ⟨112571094897424064927415923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75047396598282709951610615 112571094897424064927415923)
  ·
    refine ⟨168856642346136097391123885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112571094897424064927415923 168856642346136097391123885)
    ·
      refine ⟨63321240879801036521671457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168856642346136097391123885 63321240879801036521671457)
      ·
        refine ⟨47490930659850777391253593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63321240879801036521671457 47490930659850777391253593)
        ·
          refine ⟨35618197994888083043440195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47490930659850777391253593 35618197994888083043440195)
          ·
            refine ⟨53427296992332124565160293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35618197994888083043440195 53427296992332124565160293)
            ·
              refine ⟨10017618186062273355967555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53427296992332124565160293 10017618186062273355967555)
              ·
                refine ⟨15026427279093410033951333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10017618186062273355967555 15026427279093410033951333)
                ·
                  refine ⟨2817455114830014381365875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15026427279093410033951333 2817455114830014381365875)
                  ·
                    refine ⟨4226182672245021572048813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2817455114830014381365875 4226182672245021572048813)
                    ·
                      refine ⟨1584818502091883089518305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4226182672245021572048813 1584818502091883089518305)
                      ·
                        rfl

theorem cell23_3086423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_3086423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086423 prefixEnd_3086423 := by exact prefixLift 3086423
  have htrace : WordTrace (prefixWord ++ tailWord_3086423) baseStart_3086423 baseEnd_3086423 := by
    simpa [prefixWord, tailWord_3086423, baseEnd_3086423] using wordTrace_append hprefix tailTrace_3086423
  have hstable : (prefixWord ++ tailWord_3086423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086423).length < 2 ^ (prefixWord ++ tailWord_3086423).sum := by decide
  have hdescent : baseEnd_3086423 < baseStart_3086423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086424 : List Nat := [2, 1, 2, 2, 1, 5, 3, 2, 1, 2, 2]
def baseStart_3086424 : Nat := 118140960795 + 3086424 * 2 ^ 59
def prefixEnd_3086424 : Nat := 4983230072969 + 3 ^ 40 * 3086424 * 2
def baseEnd_3086424 : Nat := 1584819015572537585605801

theorem tailTrace_3086424 : CollatzResearch.WordTrace tailWord_3086424 prefixEnd_3086424 1584819015572537585605801 := by
  unfold tailWord_3086424
  simp only [CollatzResearch.WordTrace]
  refine ⟨56285565685210221049101163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75047420913613628065468217 56285565685210221049101163)
  ·
    refine ⟨84428348527815331573651745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56285565685210221049101163 84428348527815331573651745)
    ·
      refine ⟨63321261395861498680238809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84428348527815331573651745 63321261395861498680238809)
      ·
        refine ⟨47490946046896124010179107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63321261395861498680238809 47490946046896124010179107)
        ·
          refine ⟨71236419070344186015268661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47490946046896124010179107 71236419070344186015268661)
          ·
            refine ⟨6678414287844767438931437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71236419070344186015268661 6678414287844767438931437)
            ·
              refine ⟨2504405357941787789599289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6678414287844767438931437 2504405357941787789599289)
              ·
                refine ⟨1878304018456340842199467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2504405357941787789599289 1878304018456340842199467)
                ·
                  refine ⟨2817456027684511263299201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878304018456340842199467 2817456027684511263299201)
                  ·
                    refine ⟨2113092020763383447474401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2817456027684511263299201 2113092020763383447474401)
                    ·
                      refine ⟨1584819015572537585605801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113092020763383447474401 1584819015572537585605801)
                      ·
                        rfl

theorem cell23_3086424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_3086424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086424 prefixEnd_3086424 := by exact prefixLift 3086424
  have htrace : WordTrace (prefixWord ++ tailWord_3086424) baseStart_3086424 baseEnd_3086424 := by
    simpa [prefixWord, tailWord_3086424, baseEnd_3086424] using wordTrace_append hprefix tailTrace_3086424
  have hstable : (prefixWord ++ tailWord_3086424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086424).length < 2 ^ (prefixWord ++ tailWord_3086424).sum := by decide
  have hdescent : baseEnd_3086424 < baseStart_3086424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086433 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_3086433 : Nat := 118140960795 + 3086433 * 2 ^ 59
def prefixEnd_3086433 : Nat := 4983230072969 + 3 ^ 40 * 3086433 * 2
def baseEnd_3086433 : Nat := 1584823636898428050393259

theorem tailTrace_3086433 : CollatzResearch.WordTrace tailWord_3086433 prefixEnd_3086433 1584823636898428050393259 := by
  unfold tailWord_3086433
  simp only [CollatzResearch.WordTrace]
  refine ⟨112571459627387836635279953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75047639751591891090186635 112571459627387836635279953)
  ·
    refine ⟨84428594720540877476459965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112571459627387836635279953 84428594720540877476459965)
    ·
      refine ⟨31660723020202829053672487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84428594720540877476459965 31660723020202829053672487)
      ·
        refine ⟨47491084530304243580508731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31660723020202829053672487 47491084530304243580508731)
        ·
          refine ⟨71236626795456365370763097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47491084530304243580508731 71236626795456365370763097)
          ·
            refine ⟨53427470096592274028072323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71236626795456365370763097 53427470096592274028072323)
            ·
              refine ⟨80141205144888411042108485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53427470096592274028072323 80141205144888411042108485)
              ·
                refine ⟨15026475964666577070395341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80141205144888411042108485 15026475964666577070395341)
                ·
                  refine ⟨5634928486749966401398253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15026475964666577070395341 5634928486749966401398253)
                  ·
                    refine ⟨2113098182531237400524345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5634928486749966401398253 2113098182531237400524345)
                    ·
                      refine ⟨1584823636898428050393259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113098182531237400524345 1584823636898428050393259)
                      ·
                        rfl

theorem cell23_3086433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_3086433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086433 prefixEnd_3086433 := by exact prefixLift 3086433
  have htrace : WordTrace (prefixWord ++ tailWord_3086433) baseStart_3086433 baseEnd_3086433 := by
    simpa [prefixWord, tailWord_3086433, baseEnd_3086433] using wordTrace_append hprefix tailTrace_3086433
  have hstable : (prefixWord ++ tailWord_3086433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086433).length < 2 ^ (prefixWord ++ tailWord_3086433).sum := by decide
  have hdescent : baseEnd_3086433 < baseStart_3086433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086434 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3086434 : Nat := 118140960795 + 3086434 * 2 ^ 59
def prefixEnd_3086434 : Nat := 4983230072969 + 3 ^ 40 * 3086434 * 2
def baseEnd_3086434 : Nat := 528274716793027515493585

theorem tailTrace_3086434 : CollatzResearch.WordTrace tailWord_3086434 prefixEnd_3086434 528274716793027515493585 := by
  unfold tailWord_3086434
  simp only [CollatzResearch.WordTrace]
  refine ⟨28142874025096053451516589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75047664066922809204044237 28142874025096053451516589)
  ·
    refine ⟨10553577759411020044318721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28142874025096053451516589 10553577759411020044318721)
    ·
      refine ⟨7915183319558265033239041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10553577759411020044318721 7915183319558265033239041)
      ·
        refine ⟨5936387489668698774929281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7915183319558265033239041 5936387489668698774929281)
        ·
          refine ⟨4452290617251524081196961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5936387489668698774929281 4452290617251524081196961)
          ·
            refine ⟨3339217962938643060897721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4452290617251524081196961 3339217962938643060897721)
            ·
              refine ⟨2504413472203982295673291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3339217962938643060897721 2504413472203982295673291)
              ·
                refine ⟨3756620208305973443509937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504413472203982295673291 3756620208305973443509937)
                ·
                  refine ⟨2817465156229480082632453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3756620208305973443509937 2817465156229480082632453)
                  ·
                    refine ⟨528274716793027515493585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2817465156229480082632453 528274716793027515493585)
                    ·
                      rfl

theorem cell23_3086434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3086434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086434 prefixEnd_3086434 := by exact prefixLift 3086434
  have htrace : WordTrace (prefixWord ++ tailWord_3086434) baseStart_3086434 baseEnd_3086434 := by
    simpa [prefixWord, tailWord_3086434, baseEnd_3086434] using wordTrace_append hprefix tailTrace_3086434
  have hstable : (prefixWord ++ tailWord_3086434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086434).length < 2 ^ (prefixWord ++ tailWord_3086434).sum := by decide
  have hdescent : baseEnd_3086434 < baseStart_3086434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3086450 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_3086450 : Nat := 118140960795 + 3086450 * 2 ^ 59
def prefixEnd_3086450 : Nat := 4983230072969 + 3 ^ 40 * 3086450 * 2
def baseEnd_3086450 : Nat := 1584832366069554483880681

theorem tailTrace_3086450 : CollatzResearch.WordTrace tailWord_3086450 prefixEnd_3086450 1584832366069554483880681 := by
  unfold tailWord_3086450
  simp only [CollatzResearch.WordTrace]
  refine ⟨28143019917081562134662201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75048053112217499025765869 28143019917081562134662201)
  ·
    refine ⟨21107264937811171600996651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28143019917081562134662201 21107264937811171600996651)
    ·
      refine ⟨31660897406716757401494977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21107264937811171600996651 31660897406716757401494977)
      ·
        refine ⟨23745673055037568051121233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31660897406716757401494977 23745673055037568051121233)
        ·
          refine ⟨17809254791278176038340925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23745673055037568051121233 17809254791278176038340925)
          ·
            refine ⟨6678470546729316014377847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17809254791278176038340925 6678470546729316014377847)
            ·
              refine ⟨10017705820093974021566771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678470546729316014377847 10017705820093974021566771)
              ·
                refine ⟨15026558730140961032350157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10017705820093974021566771 15026558730140961032350157)
                ·
                  refine ⟨5634959523802860387131309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15026558730140961032350157 5634959523802860387131309)
                  ·
                    refine ⟨2113109821426072645174241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5634959523802860387131309 2113109821426072645174241)
                    ·
                      refine ⟨1584832366069554483880681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2113109821426072645174241 1584832366069554483880681)
                      ·
                        rfl

theorem cell23_3086450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_3086450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3086450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3086450 prefixEnd_3086450 := by exact prefixLift 3086450
  have htrace : WordTrace (prefixWord ++ tailWord_3086450) baseStart_3086450 baseEnd_3086450 := by
    simpa [prefixWord, tailWord_3086450, baseEnd_3086450] using wordTrace_append hprefix tailTrace_3086450
  have hstable : (prefixWord ++ tailWord_3086450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3086450).length < 2 ^ (prefixWord ++ tailWord_3086450).sum := by decide
  have hdescent : baseEnd_3086450 < baseStart_3086450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3086450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
