import V185TrunkScan23Chunk0649

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3843437 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_3843437 : Nat := 118140960795 + 3843437 * 2 ^ 59
def prefixEnd_3843437 : Nat := 4983230072969 + 3 ^ 40 * 3843437 * 2
def baseEnd_3843437 : Nat := 1973530546274584268761861

theorem tailTrace_3843437 : CollatzResearch.WordTrace tailWord_3843437 prefixEnd_3843437 1973530546274584268761861 := by
  unfold tailWord_3843437
  simp only [CollatzResearch.WordTrace]
  refine ⟨140181663776891630625496565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93454442517927753750331043 140181663776891630625496565)
  ·
    refine ⟨13142030979083590371140303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140181663776891630625496565 13142030979083590371140303)
    ·
      refine ⟨19713046468625385556710455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13142030979083590371140303 19713046468625385556710455)
      ·
        refine ⟨29569569702938078335065683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19713046468625385556710455 29569569702938078335065683)
        ·
          refine ⟨44354354554407117502598525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29569569702938078335065683 44354354554407117502598525)
          ·
            refine ⟨16632882957902669063474447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44354354554407117502598525 16632882957902669063474447)
            ·
              refine ⟨24949324436854003595211671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16632882957902669063474447 24949324436854003595211671)
              ·
                refine ⟨37423986655281005392817507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24949324436854003595211671 37423986655281005392817507)
                ·
                  refine ⟨56135979982921508089226261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37423986655281005392817507 56135979982921508089226261)
                  ·
                    refine ⟨2631374061699445691682481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56135979982921508089226261 2631374061699445691682481)
                    ·
                      refine ⟨1973530546274584268761861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631374061699445691682481 1973530546274584268761861)
                      ·
                        rfl

theorem cell23_3843437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_3843437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843437 prefixEnd_3843437 := by exact prefixLift 3843437
  have htrace : WordTrace (prefixWord ++ tailWord_3843437) baseStart_3843437 baseEnd_3843437 := by
    simpa [prefixWord, tailWord_3843437, baseEnd_3843437] using wordTrace_append hprefix tailTrace_3843437
  have hstable : (prefixWord ++ tailWord_3843437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843437).length < 2 ^ (prefixWord ++ tailWord_3843437).sum := by decide
  have hdescent : baseEnd_3843437 < baseStart_3843437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843440 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 3]
def baseStart_3843440 : Nat := 118140960795 + 3843440 * 2 ^ 59
def prefixEnd_3843440 : Nat := 4983230072969 + 3 ^ 40 * 3843440 * 2
def baseEnd_3843440 : Nat := 1973532086716547757024347

theorem tailTrace_3843440 : CollatzResearch.WordTrace tailWord_3843440 prefixEnd_3843440 1973532086716547757024347 := by
  unfold tailWord_3843440
  simp only [CollatzResearch.WordTrace]
  refine ⟨70090886597940381068927887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93454515463920508091903849 70090886597940381068927887)
  ·
    refine ⟨105136329896910571603391831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70090886597940381068927887 105136329896910571603391831)
    ·
      refine ⟨157704494845365857405087747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105136329896910571603391831 157704494845365857405087747)
      ·
        refine ⟨236556742268048786107631621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157704494845365857405087747 236556742268048786107631621)
        ·
          refine ⟨44354389175259147395180929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236556742268048786107631621 44354389175259147395180929)
          ·
            refine ⟨33265791881444360546385697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44354389175259147395180929 33265791881444360546385697)
            ·
              refine ⟨24949343911083270409789273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33265791881444360546385697 24949343911083270409789273)
              ·
                refine ⟨18712007933312452807341955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24949343911083270409789273 18712007933312452807341955)
                ·
                  refine ⟨28068011899968679211012933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18712007933312452807341955 28068011899968679211012933)
                  ·
                    refine ⟨5262752231244127352064925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28068011899968679211012933 5262752231244127352064925)
                    ·
                      refine ⟨1973532086716547757024347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262752231244127352064925 1973532086716547757024347)
                      ·
                        rfl

theorem cell23_3843440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_3843440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843440 prefixEnd_3843440 := by exact prefixLift 3843440
  have htrace : WordTrace (prefixWord ++ tailWord_3843440) baseStart_3843440 baseEnd_3843440 := by
    simpa [prefixWord, tailWord_3843440, baseEnd_3843440] using wordTrace_append hprefix tailTrace_3843440
  have hstable : (prefixWord ++ tailWord_3843440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843440).length < 2 ^ (prefixWord ++ tailWord_3843440).sum := by decide
  have hdescent : baseEnd_3843440 < baseStart_3843440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843464 : List Nat := [2, 1, 3, 3, 1, 2, 1, 5, 1, 4]
def baseStart_3843464 : Nat := 118140960795 + 3843464 * 2 ^ 59
def prefixEnd_3843464 : Nat := 4983230072969 + 3 ^ 40 * 3843464 * 2
def baseEnd_3843464 : Nat := 657848136750751887708079

theorem tailTrace_3843464 : CollatzResearch.WordTrace tailWord_3843464 prefixEnd_3843464 657848136750751887708079 := by
  unfold tailWord_3843464
  simp only [CollatzResearch.WordTrace]
  refine ⟨70091324273896907118364723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93455099031862542824486297 70091324273896907118364723)
  ·
    refine ⟨105136986410845360677547085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70091324273896907118364723 105136986410845360677547085)
    ·
      refine ⟨39426369904067010254080157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105136986410845360677547085 39426369904067010254080157)
      ·
        refine ⟨14784888714025128845280059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39426369904067010254080157 14784888714025128845280059)
        ·
          refine ⟨22177333071037693267920089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14784888714025128845280059 22177333071037693267920089)
          ·
            refine ⟨16632999803278269950940067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22177333071037693267920089 16632999803278269950940067)
            ·
              refine ⟨24949499704917404926410101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16632999803278269950940067 24949499704917404926410101)
              ·
                refine ⟨2339015597336006711850947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24949499704917404926410101 2339015597336006711850947)
                ·
                  refine ⟨3508523396004010067776421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339015597336006711850947 3508523396004010067776421)
                  ·
                    refine ⟨657848136750751887708079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3508523396004010067776421 657848136750751887708079)
                    ·
                      rfl

theorem cell23_3843464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_3843464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843464 prefixEnd_3843464 := by exact prefixLift 3843464
  have htrace : WordTrace (prefixWord ++ tailWord_3843464) baseStart_3843464 baseEnd_3843464 := by
    simpa [prefixWord, tailWord_3843464, baseEnd_3843464] using wordTrace_append hprefix tailTrace_3843464
  have hstable : (prefixWord ++ tailWord_3843464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843464).length < 2 ^ (prefixWord ++ tailWord_3843464).sum := by decide
  have hdescent : baseEnd_3843464 < baseStart_3843464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843520 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 1, 6]
def baseStart_3843520 : Nat := 118140960795 + 3843520 * 2 ^ 59
def prefixEnd_3843520 : Nat := 4983230072969 + 3 ^ 40 * 3843520 * 2
def baseEnd_3843520 : Nat := 657857721722969148007993

theorem tailTrace_3843520 : CollatzResearch.WordTrace tailWord_3843520 prefixEnd_3843520 657857721722969148007993 := by
  unfold tailWord_3843520
  simp only [CollatzResearch.WordTrace]
  refine ⟨70092345517795467900384007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93456460690393957200512009 70092345517795467900384007)
  ·
    refine ⟨105138518276693201850576011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70092345517795467900384007 105138518276693201850576011)
    ·
      refine ⟨157707777415039802775864017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105138518276693201850576011 157707777415039802775864017)
      ·
        refine ⟨118280833061279852081898013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157707777415039802775864017 118280833061279852081898013)
        ·
          refine ⟨44355312397979944530711755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118280833061279852081898013 44355312397979944530711755)
          ·
            refine ⟨66532968596969916796067633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44355312397979944530711755 66532968596969916796067633)
            ·
              refine ⟨49899726447727437597050725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66532968596969916796067633 49899726447727437597050725)
              ·
                refine ⟨9356198708948894549447011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49899726447727437597050725 9356198708948894549447011)
                ·
                  refine ⟨14034298063423341824170517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9356198708948894549447011 14034298063423341824170517)
                  ·
                    refine ⟨657857721722969148007993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14034298063423341824170517 657857721722969148007993)
                    ·
                      rfl

theorem cell23_3843520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_3843520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843520 prefixEnd_3843520 := by exact prefixLift 3843520
  have htrace : WordTrace (prefixWord ++ tailWord_3843520) baseStart_3843520 baseEnd_3843520 := by
    simpa [prefixWord, tailWord_3843520, baseEnd_3843520] using wordTrace_append hprefix tailTrace_3843520
  have hstable : (prefixWord ++ tailWord_3843520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843520).length < 2 ^ (prefixWord ++ tailWord_3843520).sum := by decide
  have hdescent : baseEnd_3843520 < baseStart_3843520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843524 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3843524 : Nat := 118140960795 + 3843524 * 2 ^ 59
def prefixEnd_3843524 : Nat := 4983230072969 + 3 ^ 40 * 3843524 * 2
def baseEnd_3843524 : Nat := 657858406363841809457987

theorem tailTrace_3843524 : CollatzResearch.WordTrace tailWord_3843524 prefixEnd_3843524 657858406363841809457987 := by
  unfold tailWord_3843524
  simp only [CollatzResearch.WordTrace]
  refine ⟨70092418463788222241956813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93456557951717629655942417 70092418463788222241956813)
  ·
    refine ⟨26284656923920583340733805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70092418463788222241956813 26284656923920583340733805)
    ·
      refine ⟨9856746346470218752775177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26284656923920583340733805 9856746346470218752775177)
      ·
        refine ⟨7392559759852664064581383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9856746346470218752775177 7392559759852664064581383)
        ·
          refine ⟨11088839639778996096872075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392559759852664064581383 11088839639778996096872075)
          ·
            refine ⟨16633259459668494145308113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088839639778996096872075 16633259459668494145308113)
            ·
              refine ⟨12474944594751370608981085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16633259459668494145308113 12474944594751370608981085)
              ·
                refine ⟨4678104223031763978367907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12474944594751370608981085 4678104223031763978367907)
                ·
                  refine ⟨7017156334547645967551861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678104223031763978367907 7017156334547645967551861)
                  ·
                    refine ⟨657858406363841809457987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7017156334547645967551861 657858406363841809457987)
                    ·
                      rfl

theorem cell23_3843524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3843524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843524 prefixEnd_3843524 := by exact prefixLift 3843524
  have htrace : WordTrace (prefixWord ++ tailWord_3843524) baseStart_3843524 baseEnd_3843524 := by
    simpa [prefixWord, tailWord_3843524, baseEnd_3843524] using wordTrace_append hprefix tailTrace_3843524
  have hstable : (prefixWord ++ tailWord_3843524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843524).length < 2 ^ (prefixWord ++ tailWord_3843524).sum := by decide
  have hdescent : baseEnd_3843524 < baseStart_3843524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843527 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_3843527 : Nat := 118140960795 + 3843527 * 2 ^ 59
def prefixEnd_3843527 : Nat := 4983230072969 + 3 ^ 40 * 3843527 * 2
def baseEnd_3843527 : Nat := 1973576759533488916636447

theorem tailTrace_3843527 : CollatzResearch.WordTrace tailWord_3843527 prefixEnd_3843527 1973576759533488916636447 := by
  unfold tailWord_3843527
  simp only [CollatzResearch.WordTrace]
  refine ⟨140184946346565575996272835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93456630897710383997515223 140184946346565575996272835)
  ·
    refine ⟨210277419519848363994409253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140184946346565575996272835 210277419519848363994409253)
    ·
      refine ⟨39427016159971568248951735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210277419519848363994409253 39427016159971568248951735)
      ·
        refine ⟨59140524239957352373427603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39427016159971568248951735 59140524239957352373427603)
        ·
          refine ⟨88710786359936028560141405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59140524239957352373427603 88710786359936028560141405)
          ·
            refine ⟨33266544884976010710053027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88710786359936028560141405 33266544884976010710053027)
            ·
              refine ⟨49899817327464016065079541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33266544884976010710053027 49899817327464016065079541)
              ·
                refine ⟨4678107874449751506101207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49899817327464016065079541 4678107874449751506101207)
                ·
                  refine ⟨7017161811674627259151811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678107874449751506101207 7017161811674627259151811)
                  ·
                    refine ⟨10525742717511940888727717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7017161811674627259151811 10525742717511940888727717)
                    ·
                      refine ⟨1973576759533488916636447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10525742717511940888727717 1973576759533488916636447)
                      ·
                        rfl

theorem cell23_3843527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_3843527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843527 prefixEnd_3843527 := by exact prefixLift 3843527
  have htrace : WordTrace (prefixWord ++ tailWord_3843527) baseStart_3843527 baseEnd_3843527 := by
    simpa [prefixWord, tailWord_3843527, baseEnd_3843527] using wordTrace_append hprefix tailTrace_3843527
  have hstable : (prefixWord ++ tailWord_3843527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843527).length < 2 ^ (prefixWord ++ tailWord_3843527).sum := by decide
  have hdescent : baseEnd_3843527 < baseStart_3843527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843557 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3843557 : Nat := 118140960795 + 3843557 * 2 ^ 59
def prefixEnd_3843557 : Nat := 4983230072969 + 3 ^ 40 * 3843557 * 2
def baseEnd_3843557 : Nat := 1973592163953123799261309

theorem tailTrace_3843557 : CollatzResearch.WordTrace tailWord_3843557 prefixEnd_3843557 1973592163953123799261309 := by
  unfold tailWord_3843557
  simp only [CollatzResearch.WordTrace]
  refine ⟨140186040536456891119864925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93457360357637927413243283 140186040536456891119864925)
  ·
    refine ⟨52569765201171334169949347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140186040536456891119864925 52569765201171334169949347)
    ·
      refine ⟨78854647801757001254924021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52569765201171334169949347 78854647801757001254924021)
      ·
        refine ⟨7392623231414718867649127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78854647801757001254924021 7392623231414718867649127)
        ·
          refine ⟨11088934847122078301473691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392623231414718867649127 11088934847122078301473691)
          ·
            refine ⟨16633402270683117452210537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088934847122078301473691 16633402270683117452210537)
            ·
              refine ⟨12475051703012338089157903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16633402270683117452210537 12475051703012338089157903)
              ·
                refine ⟨18712577554518507133736855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12475051703012338089157903 18712577554518507133736855)
                ·
                  refine ⟨28068866331777760700605283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18712577554518507133736855 28068866331777760700605283)
                  ·
                    refine ⟨42103299497666641050907925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28068866331777760700605283 42103299497666641050907925)
                    ·
                      refine ⟨1973592163953123799261309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42103299497666641050907925 1973592163953123799261309)
                      ·
                        rfl

theorem cell23_3843557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3843557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843557 prefixEnd_3843557 := by exact prefixLift 3843557
  have htrace : WordTrace (prefixWord ++ tailWord_3843557) baseStart_3843557 baseEnd_3843557 := by
    simpa [prefixWord, tailWord_3843557, baseEnd_3843557] using wordTrace_append hprefix tailTrace_3843557
  have hstable : (prefixWord ++ tailWord_3843557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843557).length < 2 ^ (prefixWord ++ tailWord_3843557).sum := by decide
  have hdescent : baseEnd_3843557 < baseStart_3843557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843574 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3843574 : Nat := 118140960795 + 3843574 * 2 ^ 59
def prefixEnd_3843574 : Nat := 4983230072969 + 3 ^ 40 * 3843574 * 2
def baseEnd_3843574 : Nat := 1973600893124250232748731

theorem tailTrace_3843574 : CollatzResearch.WordTrace tailWord_3843574 prefixEnd_3843574 1973600893124250232748731 := by
  unfold tailWord_3843574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8761666286087206438952111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93457773718263535348822517 8761666286087206438952111)
  ·
    refine ⟨13142499429130809658428167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8761666286087206438952111 13142499429130809658428167)
    ·
      refine ⟨19713749143696214487642251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13142499429130809658428167 19713749143696214487642251)
      ·
        refine ⟨29570623715544321731463377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19713749143696214487642251 29570623715544321731463377)
        ·
          refine ⟨22177967786658241298597533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29570623715544321731463377 22177967786658241298597533)
          ·
            refine ⟨8316737919996840486974075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22177967786658241298597533 8316737919996840486974075)
            ·
              refine ⟨12475106879995260730461113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8316737919996840486974075 12475106879995260730461113)
              ·
                refine ⟨9356330159996445547845835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12475106879995260730461113 9356330159996445547845835)
                ·
                  refine ⟨14034495239994668321768753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9356330159996445547845835 14034495239994668321768753)
                  ·
                    refine ⟨10525871429996001241326565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14034495239994668321768753 10525871429996001241326565)
                    ·
                      refine ⟨1973600893124250232748731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10525871429996001241326565 1973600893124250232748731)
                      ·
                        rfl

theorem cell23_3843574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3843574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843574 prefixEnd_3843574 := by exact prefixLift 3843574
  have htrace : WordTrace (prefixWord ++ tailWord_3843574) baseStart_3843574 baseEnd_3843574 := by
    simpa [prefixWord, tailWord_3843574, baseEnd_3843574] using wordTrace_append hprefix tailTrace_3843574
  have hstable : (prefixWord ++ tailWord_3843574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843574).length < 2 ^ (prefixWord ++ tailWord_3843574).sum := by decide
  have hdescent : baseEnd_3843574 < baseStart_3843574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843581 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_3843581 : Nat := 118140960795 + 3843581 * 2 ^ 59
def prefixEnd_3843581 : Nat := 4983230072969 + 3 ^ 40 * 3843581 * 2
def baseEnd_3843581 : Nat := 1973604487488831705361199

theorem tailTrace_3843581 : CollatzResearch.WordTrace tailWord_3843581 prefixEnd_3843581 1973604487488831705361199 := by
  unfold tailWord_3843581
  simp only [CollatzResearch.WordTrace]
  refine ⟨140186915888369943218738597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93457943925579962145825731 140186915888369943218738597)
  ·
    refine ⟨26285046729069364353513487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140186915888369943218738597 26285046729069364353513487)
    ·
      refine ⟨39427570093604046530270231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26285046729069364353513487 39427570093604046530270231)
      ·
        refine ⟨59141355140406069795405347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39427570093604046530270231 59141355140406069795405347)
        ·
          refine ⟨88712032710609104693108021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59141355140406069795405347 88712032710609104693108021)
          ·
            refine ⟨8316753066619603564978877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88712032710609104693108021 8316753066619603564978877)
            ·
              refine ⟨3118782399982351336867079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8316753066619603564978877 3118782399982351336867079)
              ·
                refine ⟨4678173599973527005300619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118782399982351336867079 4678173599973527005300619)
                ·
                  refine ⟨7017260399960290507950929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678173599973527005300619 7017260399960290507950929)
                  ·
                    refine ⟨5262945299970217880963197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7017260399960290507950929 5262945299970217880963197)
                    ·
                      refine ⟨1973604487488831705361199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5262945299970217880963197 1973604487488831705361199)
                      ·
                        rfl

theorem cell23_3843581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_3843581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843581 prefixEnd_3843581 := by exact prefixLift 3843581
  have htrace : WordTrace (prefixWord ++ tailWord_3843581) baseStart_3843581 baseEnd_3843581 := by
    simpa [prefixWord, tailWord_3843581, baseEnd_3843581] using wordTrace_append hprefix tailTrace_3843581
  have hstable : (prefixWord ++ tailWord_3843581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843581).length < 2 ^ (prefixWord ++ tailWord_3843581).sum := by decide
  have hdescent : baseEnd_3843581 < baseStart_3843581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843645 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_3843645 : Nat := 118140960795 + 3843645 * 2 ^ 59
def prefixEnd_3843645 : Nat := 4983230072969 + 3 ^ 40 * 3843645 * 2
def baseEnd_3843645 : Nat := 1973637350250719454960905

theorem tailTrace_3843645 : CollatzResearch.WordTrace tailWord_3843645 prefixEnd_3843645 1973637350250719454960905 := by
  unfold tailWord_3843645
  simp only [CollatzResearch.WordTrace]
  refine ⟨140189250160138082149068389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93459500106758721432712259 140189250160138082149068389)
  ·
    refine ⟨26285484405025890402950323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140189250160138082149068389 26285484405025890402950323)
    ·
      refine ⟨39428226607538835604425485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26285484405025890402950323 39428226607538835604425485)
      ·
        refine ⟨14785584977827063351659557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39428226607538835604425485 14785584977827063351659557)
        ·
          refine ⟨2772297183342574378436167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14785584977827063351659557 2772297183342574378436167)
          ·
            refine ⟨4158445775013861567654251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772297183342574378436167 4158445775013861567654251)
            ·
              refine ⟨6237668662520792351481377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158445775013861567654251 6237668662520792351481377)
              ·
                refine ⟨4678251496890594263611033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6237668662520792351481377 4678251496890594263611033)
                ·
                  refine ⟨3508688622667945697708275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4678251496890594263611033 3508688622667945697708275)
                  ·
                    refine ⟨5263032934001918546562413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3508688622667945697708275 5263032934001918546562413)
                    ·
                      refine ⟨1973637350250719454960905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5263032934001918546562413 1973637350250719454960905)
                      ·
                        rfl

theorem cell23_3843645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_3843645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843645 prefixEnd_3843645 := by exact prefixLift 3843645
  have htrace : WordTrace (prefixWord ++ tailWord_3843645) baseStart_3843645 baseEnd_3843645 := by
    simpa [prefixWord, tailWord_3843645, baseEnd_3843645] using wordTrace_append hprefix tailTrace_3843645
  have hstable : (prefixWord ++ tailWord_3843645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843645).length < 2 ^ (prefixWord ++ tailWord_3843645).sum := by decide
  have hdescent : baseEnd_3843645 < baseStart_3843645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843647 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_3843647 : Nat := 118140960795 + 3843647 * 2 ^ 59
def prefixEnd_3843647 : Nat := 4983230072969 + 3 ^ 40 * 3843647 * 2
def baseEnd_3843647 : Nat := 1973638377212028447135895

theorem tailTrace_3843647 : CollatzResearch.WordTrace tailWord_3843647 prefixEnd_3843647 1973638377212028447135895 := by
  unfold tailWord_3843647
  simp only [CollatzResearch.WordTrace]
  refine ⟨140189323106130836490641195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93459548737420557660427463 140189323106130836490641195)
  ·
    refine ⟨210283984659196254735961793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140189323106130836490641195 210283984659196254735961793)
    ·
      refine ⟨157712988494397191051971345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210283984659196254735961793 157712988494397191051971345)
      ·
        refine ⟨118284741370797893288978509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157712988494397191051971345 118284741370797893288978509)
        ·
          refine ⟨44356778014049209983366941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118284741370797893288978509 44356778014049209983366941)
          ·
            refine ⟨16633791755268453743762603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44356778014049209983366941 16633791755268453743762603)
            ·
              refine ⟨24950687632902680615643905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16633791755268453743762603 24950687632902680615643905)
              ·
                refine ⟨18713015724677010461732929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24950687632902680615643905 18713015724677010461732929)
                ·
                  refine ⟨14034761793507757846299697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18713015724677010461732929 14034761793507757846299697)
                  ·
                    refine ⟨10526071345130818384724773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14034761793507757846299697 10526071345130818384724773)
                    ·
                      refine ⟨1973638377212028447135895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10526071345130818384724773 1973638377212028447135895)
                      ·
                        rfl

theorem cell23_3843647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_3843647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843647 prefixEnd_3843647 := by exact prefixLift 3843647
  have htrace : WordTrace (prefixWord ++ tailWord_3843647) baseStart_3843647 baseEnd_3843647 := by
    simpa [prefixWord, tailWord_3843647, baseEnd_3843647] using wordTrace_append hprefix tailTrace_3843647
  have hstable : (prefixWord ++ tailWord_3843647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843647).length < 2 ^ (prefixWord ++ tailWord_3843647).sum := by decide
  have hdescent : baseEnd_3843647 < baseStart_3843647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843687 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 1, 7]
def baseStart_3843687 : Nat := 118140960795 + 3843687 * 2 ^ 59
def prefixEnd_3843687 : Nat := 4983230072969 + 3 ^ 40 * 3843687 * 2
def baseEnd_3843687 : Nat := 657886305479402763545237

theorem tailTrace_3843687 : CollatzResearch.WordTrace tailWord_3843687 prefixEnd_3843687 657886305479402763545237 := by
  unfold tailWord_3843687
  simp only [CollatzResearch.WordTrace]
  refine ⟨140190782025985923322097315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93460521350657282214731543 140190782025985923322097315)
  ·
    refine ⟨210286173038978884983145973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140190782025985923322097315 210286173038978884983145973)
    ·
      refine ⟨19714328722404270467169935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210286173038978884983145973 19714328722404270467169935)
      ·
        refine ⟨29571493083606405700754903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19714328722404270467169935 29571493083606405700754903)
        ·
          refine ⟨44357239625409608551132355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29571493083606405700754903 44357239625409608551132355)
          ·
            refine ⟨66535859438114412826698533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44357239625409608551132355 66535859438114412826698533)
            ·
              refine ⟨12475473644646452405005975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66535859438114412826698533 12475473644646452405005975)
              ·
                refine ⟨18713210466969678607508963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12475473644646452405005975 18713210466969678607508963)
                ·
                  refine ⟨28069815700454517911263445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18713210466969678607508963 28069815700454517911263445)
                  ·
                    refine ⟨657886305479402763545237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28069815700454517911263445 657886305479402763545237)
                    ·
                      rfl

theorem cell23_3843687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_3843687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843687 prefixEnd_3843687 := by exact prefixLift 3843687
  have htrace : WordTrace (prefixWord ++ tailWord_3843687) baseStart_3843687 baseEnd_3843687 := by
    simpa [prefixWord, tailWord_3843687, baseEnd_3843687] using wordTrace_append hprefix tailTrace_3843687
  have hstable : (prefixWord ++ tailWord_3843687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843687).length < 2 ^ (prefixWord ++ tailWord_3843687).sum := by decide
  have hdescent : baseEnd_3843687 < baseStart_3843687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843724 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 1, 6, 2]
def baseStart_3843724 : Nat := 118140960795 + 3843724 * 2 ^ 59
def prefixEnd_3843724 : Nat := 4983230072969 + 3 ^ 40 * 3843724 * 2
def baseEnd_3843724 : Nat := 1973677915222424645873041

theorem tailTrace_3843724 : CollatzResearch.WordTrace tailWord_3843724 prefixEnd_3843724 1973677915222424645873041 := by
  unfold tailWord_3843724
  simp only [CollatzResearch.WordTrace]
  refine ⟨70096065763425939320597113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93461421017901252427462817 70096065763425939320597113)
  ·
    refine ⟨52572049322569454490447835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70096065763425939320597113 52572049322569454490447835)
    ·
      refine ⟨78858073983854181735671753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52572049322569454490447835 78858073983854181735671753)
      ·
        refine ⟨59143555487890636301753815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78858073983854181735671753 59143555487890636301753815)
        ·
          refine ⟨88715333231835954452630723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59143555487890636301753815 88715333231835954452630723)
          ·
            refine ⟨133072999847753931678946085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88715333231835954452630723 133072999847753931678946085)
            ·
              refine ⟨24951187471453862189802391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133072999847753931678946085 24951187471453862189802391)
              ·
                refine ⟨37426781207180793284703587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24951187471453862189802391 37426781207180793284703587)
                ·
                  refine ⟨56140171810771189927055381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37426781207180793284703587 56140171810771189927055381)
                  ·
                    refine ⟨2631570553629899527830721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56140171810771189927055381 2631570553629899527830721)
                    ·
                      refine ⟨1973677915222424645873041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631570553629899527830721 1973677915222424645873041)
                      ·
                        rfl

theorem cell23_3843724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_3843724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843724 prefixEnd_3843724 := by exact prefixLift 3843724
  have htrace : WordTrace (prefixWord ++ tailWord_3843724) baseStart_3843724 baseEnd_3843724 := by
    simpa [prefixWord, tailWord_3843724, baseEnd_3843724] using wordTrace_append hprefix tailTrace_3843724
  have hstable : (prefixWord ++ tailWord_3843724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843724).length < 2 ^ (prefixWord ++ tailWord_3843724).sum := by decide
  have hdescent : baseEnd_3843724 < baseStart_3843724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843801 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 1, 5, 2]
def baseStart_3843801 : Nat := 118140960795 + 3843801 * 2 ^ 59
def prefixEnd_3843801 : Nat := 4983230072969 + 3 ^ 40 * 3843801 * 2
def baseEnd_3843801 : Nat := 1973717453232820844610187

theorem tailTrace_3843801 : CollatzResearch.WordTrace tailWord_3843801 prefixEnd_3843801 1973717453232820844610187 := by
  unfold tailWord_3843801
  simp only [CollatzResearch.WordTrace]
  refine ⟨140194939947572920791747257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93463293298381947194498171 140194939947572920791747257)
  ·
    refine ⟨105146204960679690593810443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140194939947572920791747257 105146204960679690593810443)
    ·
      refine ⟨157719307441019535890715665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105146204960679690593810443 157719307441019535890715665)
      ·
        refine ⟨118289480580764651918036749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157719307441019535890715665 118289480580764651918036749)
        ·
          refine ⟨44358555217786744469263781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118289480580764651918036749 44358555217786744469263781)
          ·
            refine ⟨8317229103335014587986959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44358555217786744469263781 8317229103335014587986959)
            ·
              refine ⟨12475843655002521881980439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8317229103335014587986959 12475843655002521881980439)
              ·
                refine ⟨18713765482503782822970659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12475843655002521881980439 18713765482503782822970659)
                ·
                  refine ⟨28070648223755674234455989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18713765482503782822970659 28070648223755674234455989)
                  ·
                    refine ⟨2631623270977094459480249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28070648223755674234455989 2631623270977094459480249)
                    ·
                      refine ⟨1973717453232820844610187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631623270977094459480249 1973717453232820844610187)
                      ·
                        rfl

theorem cell23_3843801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_3843801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843801 prefixEnd_3843801 := by exact prefixLift 3843801
  have htrace : WordTrace (prefixWord ++ tailWord_3843801) baseStart_3843801 baseEnd_3843801 := by
    simpa [prefixWord, tailWord_3843801, baseEnd_3843801] using wordTrace_append hprefix tailTrace_3843801
  have hstable : (prefixWord ++ tailWord_3843801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843801).length < 2 ^ (prefixWord ++ tailWord_3843801).sum := by decide
  have hdescent : baseEnd_3843801 < baseStart_3843801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843808 : List Nat := [2, 1, 1, 3, 1, 2, 3, 5, 1, 1, 3]
def baseStart_3843808 : Nat := 118140960795 + 3843808 * 2 ^ 59
def prefixEnd_3843808 : Nat := 4983230072969 + 3 ^ 40 * 3843808 * 2
def baseEnd_3843808 : Nat := 1973721047597402317222655

theorem tailTrace_3843808 : CollatzResearch.WordTrace tailWord_3843808 prefixEnd_3843808 1973721047597402317222655 := by
  unfold tailWord_3843808
  simp only [CollatzResearch.WordTrace]
  refine ⟨70097597629273780493626039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93463463505698373991501385 70097597629273780493626039)
  ·
    refine ⟨105146396443910670740439059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70097597629273780493626039 105146396443910670740439059)
    ·
      refine ⟨157719594665866006110658589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105146396443910670740439059 157719594665866006110658589)
      ·
        refine ⟨59144847999699752291496971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157719594665866006110658589 59144847999699752291496971)
        ·
          refine ⟨88717271999549628437245457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59144847999699752291496971 88717271999549628437245457)
          ·
            refine ⟨66537953999662221327934093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88717271999549628437245457 66537953999662221327934093)
            ·
              refine ⟨24951732749873332997975285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66537953999662221327934093 24951732749873332997975285)
              ·
                refine ⟨2339224945300624968560183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24951732749873332997975285 2339224945300624968560183)
                ·
                  refine ⟨3508837417950937452840275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339224945300624968560183 3508837417950937452840275)
                  ·
                    refine ⟨5263256126926406179260413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3508837417950937452840275 5263256126926406179260413)
                    ·
                      refine ⟨1973721047597402317222655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5263256126926406179260413 1973721047597402317222655)
                      ·
                        rfl

theorem cell23_3843808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_3843808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843808 prefixEnd_3843808 := by exact prefixLift 3843808
  have htrace : WordTrace (prefixWord ++ tailWord_3843808) baseStart_3843808 baseEnd_3843808 := by
    simpa [prefixWord, tailWord_3843808, baseEnd_3843808] using wordTrace_append hprefix tailTrace_3843808
  have hstable : (prefixWord ++ tailWord_3843808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843808).length < 2 ^ (prefixWord ++ tailWord_3843808).sum := by decide
  have hdescent : baseEnd_3843808 < baseStart_3843808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843815 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 6]
def baseStart_3843815 : Nat := 118140960795 + 3843815 * 2 ^ 59
def prefixEnd_3843815 : Nat := 4983230072969 + 3 ^ 40 * 3843815 * 2
def baseEnd_3843815 : Nat := 219302737995775976648347

theorem tailTrace_3843815 : CollatzResearch.WordTrace tailWord_3843815 prefixEnd_3843815 219302737995775976648347 := by
  unfold tailWord_3843815
  simp only [CollatzResearch.WordTrace]
  refine ⟨140195450569522201182756899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93463633713014800788504599 140195450569522201182756899)
  ·
    refine ⟨210293175854283301774135349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140195450569522201182756899 210293175854283301774135349)
    ·
      refine ⟨19714985236339059541325189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210293175854283301774135349 19714985236339059541325189)
      ·
        refine ⟨3696559731813573663998473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19714985236339059541325189 3696559731813573663998473)
        ·
          refine ⟨2772419798860180247998855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3696559731813573663998473 2772419798860180247998855)
          ·
            refine ⟨4158629698290270371998283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772419798860180247998855 4158629698290270371998283)
            ·
              refine ⟨6237944547435405557997425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158629698290270371998283 6237944547435405557997425)
              ·
                refine ⟨4678458410576554168498069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6237944547435405557997425 4678458410576554168498069)
                ·
                  refine ⟨219302737995775976648347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4678458410576554168498069 219302737995775976648347)
                  ·
                    rfl

theorem cell23_3843815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 6].length) (baseStart_3843815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843815 prefixEnd_3843815 := by exact prefixLift 3843815
  have htrace : WordTrace (prefixWord ++ tailWord_3843815) baseStart_3843815 baseEnd_3843815 := by
    simpa [prefixWord, tailWord_3843815, baseEnd_3843815] using wordTrace_append hprefix tailTrace_3843815
  have hstable : (prefixWord ++ tailWord_3843815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843815).length < 2 ^ (prefixWord ++ tailWord_3843815).sum := by decide
  have hdescent : baseEnd_3843815 < baseStart_3843815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843841 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3843841 : Nat := 118140960795 + 3843841 * 2 ^ 59
def prefixEnd_3843841 : Nat := 4983230072969 + 3 ^ 40 * 3843841 * 2
def baseEnd_3843841 : Nat := 657912664153000229370001

theorem tailTrace_3843841 : CollatzResearch.WordTrace tailWord_3843841 prefixEnd_3843841 657912664153000229370001 := by
  unfold tailWord_3843841
  simp only [CollatzResearch.WordTrace]
  refine ⟨140196398867428007623203377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93464265911618671748802251 140196398867428007623203377)
  ·
    refine ⟨105147299150571005717402533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140196398867428007623203377 105147299150571005717402533)
    ·
      refine ⟨19715118590732063572012975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105147299150571005717402533 19715118590732063572012975)
      ·
        refine ⟨29572677886098095358019463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19715118590732063572012975 29572677886098095358019463)
        ·
          refine ⟨44359016829147143037029195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29572677886098095358019463 44359016829147143037029195)
          ·
            refine ⟨66538525243720714555543793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44359016829147143037029195 66538525243720714555543793)
            ·
              refine ⟨49903893932790535916657845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66538525243720714555543793 49903893932790535916657845)
              ·
                refine ⟨4678490056199112742186673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49903893932790535916657845 4678490056199112742186673)
                ·
                  refine ⟨3508867542149334556640005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4678490056199112742186673 3508867542149334556640005)
                  ·
                    refine ⟨657912664153000229370001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3508867542149334556640005 657912664153000229370001)
                    ·
                      rfl

theorem cell23_3843841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3843841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843841 prefixEnd_3843841 := by exact prefixLift 3843841
  have htrace : WordTrace (prefixWord ++ tailWord_3843841) baseStart_3843841 baseEnd_3843841 := by
    simpa [prefixWord, tailWord_3843841, baseEnd_3843841] using wordTrace_append hprefix tailTrace_3843841
  have hstable : (prefixWord ++ tailWord_3843841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843841).length < 2 ^ (prefixWord ++ tailWord_3843841).sum := by decide
  have hdescent : baseEnd_3843841 < baseStart_3843841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843848 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_3843848 : Nat := 118140960795 + 3843848 * 2 ^ 59
def prefixEnd_3843848 : Nat := 4983230072969 + 3 ^ 40 * 3843848 * 2
def baseEnd_3843848 : Nat := 1973741586823582160722471

theorem tailTrace_3843848 : CollatzResearch.WordTrace tailWord_3843848 prefixEnd_3843848 1973741586823582160722471 := by
  unfold tailWord_3843848
  simp only [CollatzResearch.WordTrace]
  refine ⟨70098327089201323909354099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93464436118935098545805465 70098327089201323909354099)
  ·
    refine ⟨105147490633801985864031149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70098327089201323909354099 105147490633801985864031149)
    ·
      refine ⟨39430308987675744699011681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105147490633801985864031149 39430308987675744699011681)
      ·
        refine ⟨29572731740756808524258761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39430308987675744699011681 29572731740756808524258761)
        ·
          refine ⟨22179548805567606393194071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29572731740756808524258761 22179548805567606393194071)
          ·
            refine ⟨33269323208351409589791107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22179548805567606393194071 33269323208351409589791107)
            ·
              refine ⟨49903984812527114384686661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33269323208351409589791107 49903984812527114384686661)
              ·
                refine ⟨9356997152348833947128749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49903984812527114384686661 9356997152348833947128749)
                ·
                  refine ⟨3508873932130812730173281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9356997152348833947128749 3508873932130812730173281)
                  ·
                    refine ⟨2631655449098109547629961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3508873932130812730173281 2631655449098109547629961)
                    ·
                      refine ⟨1973741586823582160722471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631655449098109547629961 1973741586823582160722471)
                      ·
                        rfl

theorem cell23_3843848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_3843848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843848 prefixEnd_3843848 := by exact prefixLift 3843848
  have htrace : WordTrace (prefixWord ++ tailWord_3843848) baseStart_3843848 baseEnd_3843848 := by
    simpa [prefixWord, tailWord_3843848, baseEnd_3843848] using wordTrace_append hprefix tailTrace_3843848
  have hstable : (prefixWord ++ tailWord_3843848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843848).length < 2 ^ (prefixWord ++ tailWord_3843848).sum := by decide
  have hdescent : baseEnd_3843848 < baseStart_3843848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843851 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 3]
def baseStart_3843851 : Nat := 118140960795 + 3843851 * 2 ^ 59
def prefixEnd_3843851 : Nat := 4983230072969 + 3 ^ 40 * 3843851 * 2
def baseEnd_3843851 : Nat := 1973743127265545648984957

theorem tailTrace_3843851 : CollatzResearch.WordTrace tailWord_3843851 prefixEnd_3843851 1973743127265545648984957 := by
  unfold tailWord_3843851
  simp only [CollatzResearch.WordTrace]
  refine ⟨140196763597391779331067407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93464509064927852887378271 140196763597391779331067407)
  ·
    refine ⟨210295145396087668996601111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140196763597391779331067407 210295145396087668996601111)
    ·
      refine ⟨315442718094131503494901667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210295145396087668996601111 315442718094131503494901667)
      ·
        refine ⟨473164077141197255242352501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315442718094131503494901667 473164077141197255242352501)
        ·
          refine ⟨44359132231987242678970547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 473164077141197255242352501 44359132231987242678970547)
          ·
            refine ⟨66538698347980864018455821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44359132231987242678970547 66538698347980864018455821)
            ·
              refine ⟨24952011880492824006920933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66538698347980864018455821 24952011880492824006920933)
              ·
                refine ⟨4678502227592404501297675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24952011880492824006920933 4678502227592404501297675)
                ·
                  refine ⟨7017753341388606751946513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678502227592404501297675 7017753341388606751946513)
                  ·
                    refine ⟨5263315006041455063959885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7017753341388606751946513 5263315006041455063959885)
                    ·
                      refine ⟨1973743127265545648984957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5263315006041455063959885 1973743127265545648984957)
                      ·
                        rfl

theorem cell23_3843851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 3].length) (baseStart_3843851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843851 prefixEnd_3843851 := by exact prefixLift 3843851
  have htrace : WordTrace (prefixWord ++ tailWord_3843851) baseStart_3843851 baseEnd_3843851 := by
    simpa [prefixWord, tailWord_3843851, baseEnd_3843851] using wordTrace_append hprefix tailTrace_3843851
  have hstable : (prefixWord ++ tailWord_3843851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843851).length < 2 ^ (prefixWord ++ tailWord_3843851).sum := by decide
  have hdescent : baseEnd_3843851 < baseStart_3843851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843853 : List Nat := [1, 7, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3843853 : Nat := 118140960795 + 3843853 * 2 ^ 59
def prefixEnd_3843853 : Nat := 4983230072969 + 3 ^ 40 * 3843853 * 2
def baseEnd_3843853 : Nat := 657914718075618213719983

theorem tailTrace_3843853 : CollatzResearch.WordTrace tailWord_3843853 prefixEnd_3843853 657914718075618213719983 := by
  unfold tailWord_3843853
  simp only [CollatzResearch.WordTrace]
  refine ⟨140196836543384533672640213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93464557695589689115093475 140196836543384533672640213)
  ·
    refine ⟨3285863356485575007952505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 140196836543384533672640213 3285863356485575007952505)
    ·
      refine ⟨2464397517364181255964379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3285863356485575007952505 2464397517364181255964379)
      ·
        refine ⟨3696596276046271883946569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464397517364181255964379 3696596276046271883946569)
        ·
          refine ⟨2772447207034703912959927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3696596276046271883946569 2772447207034703912959927)
          ·
            refine ⟨4158670810552055869439891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772447207034703912959927 4158670810552055869439891)
            ·
              refine ⟨6238006215828083804159837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158670810552055869439891 6238006215828083804159837)
              ·
                refine ⟨2339252330935531426559939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6238006215828083804159837 2339252330935531426559939)
                ·
                  refine ⟨3508878496403297139839909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339252330935531426559939 3508878496403297139839909)
                  ·
                    refine ⟨657914718075618213719983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3508878496403297139839909 657914718075618213719983)
                    ·
                      rfl

theorem cell23_3843853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3843853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843853 prefixEnd_3843853 := by exact prefixLift 3843853
  have htrace : WordTrace (prefixWord ++ tailWord_3843853) baseStart_3843853 baseEnd_3843853 := by
    simpa [prefixWord, tailWord_3843853, baseEnd_3843853] using wordTrace_append hprefix tailTrace_3843853
  have hstable : (prefixWord ++ tailWord_3843853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843853).length < 2 ^ (prefixWord ++ tailWord_3843853).sum := by decide
  have hdescent : baseEnd_3843853 < baseStart_3843853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843858 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3843858 : Nat := 118140960795 + 3843858 * 2 ^ 59
def prefixEnd_3843858 : Nat := 4983230072969 + 3 ^ 40 * 3843858 * 2
def baseEnd_3843858 : Nat := 657915573876709040532475

theorem tailTrace_3843858 : CollatzResearch.WordTrace tailWord_3843858 prefixEnd_3843858 657915573876709040532475 := by
  unfold tailWord_3843858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35049254727091604881643057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93464679272244279684381485 35049254727091604881643057)
  ·
    refine ⟨26286941045318703661232293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35049254727091604881643057 26286941045318703661232293)
    ·
      refine ⟨4928801445997256936481055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26286941045318703661232293 4928801445997256936481055)
      ·
        refine ⟨7393202168995885404721583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4928801445997256936481055 7393202168995885404721583)
        ·
          refine ⟨11089803253493828107082375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393202168995885404721583 11089803253493828107082375)
          ·
            refine ⟨16634704880240742160623563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11089803253493828107082375 16634704880240742160623563)
            ·
              refine ⟨24952057320361113240935345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16634704880240742160623563 24952057320361113240935345)
              ·
                refine ⟨18714042990270834930701509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24952057320361113240935345 18714042990270834930701509)
                ·
                  refine ⟨3508883060675781549506533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18714042990270834930701509 3508883060675781549506533)
                  ·
                    refine ⟨657915573876709040532475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3508883060675781549506533 657915573876709040532475)
                    ·
                      rfl

theorem cell23_3843858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3843858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843858 prefixEnd_3843858 := by exact prefixLift 3843858
  have htrace : WordTrace (prefixWord ++ tailWord_3843858) baseStart_3843858 baseEnd_3843858 := by
    simpa [prefixWord, tailWord_3843858, baseEnd_3843858] using wordTrace_append hprefix tailTrace_3843858
  have hstable : (prefixWord ++ tailWord_3843858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843858).length < 2 ^ (prefixWord ++ tailWord_3843858).sum := by decide
  have hdescent : baseEnd_3843858 < baseStart_3843858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843892 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_3843892 : Nat := 118140960795 + 3843892 * 2 ^ 59
def prefixEnd_3843892 : Nat := 4983230072969 + 3 ^ 40 * 3843892 * 2
def baseEnd_3843892 : Nat := 657921393324126662857423

theorem tailTrace_3843892 : CollatzResearch.WordTrace tailWord_3843892 prefixEnd_3843892 657921393324126662857423 := by
  unfold tailWord_3843892
  simp only [CollatzResearch.WordTrace]
  refine ⟨70099129495121621666654965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93465505993495495555539953 70099129495121621666654965)
  ·
    refine ⟨6571793390167652031248903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70099129495121621666654965 6571793390167652031248903)
    ·
      refine ⟨9857690085251478046873355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6571793390167652031248903 9857690085251478046873355)
      ·
        refine ⟨14786535127877217070310033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9857690085251478046873355 14786535127877217070310033)
        ·
          refine ⟨11089901345907912802732525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14786535127877217070310033 11089901345907912802732525)
          ·
            refine ⟨4158713004715467301024697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11089901345907912802732525 4158713004715467301024697)
            ·
              refine ⟨3119034753536600475768523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158713004715467301024697 3119034753536600475768523)
              ·
                refine ⟨4678552130304900713652785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119034753536600475768523 4678552130304900713652785)
                ·
                  refine ⟨3508914097728675535239589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4678552130304900713652785 3508914097728675535239589)
                  ·
                    refine ⟨657921393324126662857423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3508914097728675535239589 657921393324126662857423)
                    ·
                      rfl

theorem cell23_3843892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_3843892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843892 prefixEnd_3843892 := by exact prefixLift 3843892
  have htrace : WordTrace (prefixWord ++ tailWord_3843892) baseStart_3843892 baseEnd_3843892 := by
    simpa [prefixWord, tailWord_3843892, baseEnd_3843892] using wordTrace_append hprefix tailTrace_3843892
  have hstable : (prefixWord ++ tailWord_3843892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843892).length < 2 ^ (prefixWord ++ tailWord_3843892).sum := by decide
  have hdescent : baseEnd_3843892 < baseStart_3843892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843932 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3843932 : Nat := 118140960795 + 3843932 * 2 ^ 59
def prefixEnd_3843932 : Nat := 4983230072969 + 3 ^ 40 * 3843932 * 2
def baseEnd_3843932 : Nat := 1973784719198559832072085

theorem tailTrace_3843932 : CollatzResearch.WordTrace tailWord_3843932 prefixEnd_3843932 1973784719198559832072085 := by
  unfold tailWord_3843932
  simp only [CollatzResearch.WordTrace]
  refine ⟨70099858955049165082383025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93466478606732220109844033 70099858955049165082383025)
  ·
    refine ⟨52574894216286873811787269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70099858955049165082383025 52574894216286873811787269)
    ·
      refine ⟨9857792665553788839710113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52574894216286873811787269 9857792665553788839710113)
      ·
        refine ⟨7393344499165341629782585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9857792665553788839710113 7393344499165341629782585)
        ·
          refine ⟨5545008374374006222336939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7393344499165341629782585 5545008374374006222336939)
          ·
            refine ⟨8317512561561009333505409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545008374374006222336939 8317512561561009333505409)
            ·
              refine ⟨6238134421170757000129057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8317512561561009333505409 6238134421170757000129057)
              ·
                refine ⟨4678600815878067750096793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6238134421170757000129057 4678600815878067750096793)
                ·
                  refine ⟨3508950611908550812572595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4678600815878067750096793 3508950611908550812572595)
                  ·
                    refine ⟨5263425917862826218858893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3508950611908550812572595 5263425917862826218858893)
                    ·
                      refine ⟨1973784719198559832072085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5263425917862826218858893 1973784719198559832072085)
                      ·
                        rfl

theorem cell23_3843932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3843932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843932 prefixEnd_3843932 := by exact prefixLift 3843932
  have htrace : WordTrace (prefixWord ++ tailWord_3843932) baseStart_3843932 baseEnd_3843932 := by
    simpa [prefixWord, tailWord_3843932, baseEnd_3843932] using wordTrace_append hprefix tailTrace_3843932
  have hstable : (prefixWord ++ tailWord_3843932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843932).length < 2 ^ (prefixWord ++ tailWord_3843932).sum := by decide
  have hdescent : baseEnd_3843932 < baseStart_3843932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3843988 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3843988 : Nat := 118140960795 + 3843988 * 2 ^ 59
def prefixEnd_3843988 : Nat := 4983230072969 + 3 ^ 40 * 3843988 * 2
def baseEnd_3843988 : Nat := 1973813474115211612971827

theorem tailTrace_3843988 : CollatzResearch.WordTrace tailWord_3843988 prefixEnd_3843988 1973813474115211612971827 := by
  unfold tailWord_3843988
  simp only [CollatzResearch.WordTrace]
  refine ⟨70100880198947725864402309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93467840265263634485869745 70100880198947725864402309)
  ·
    refine ⟨13143915037302698599575433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70100880198947725864402309 13143915037302698599575433)
    ·
      refine ⟨9857936277977023949681575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13143915037302698599575433 9857936277977023949681575)
      ·
        refine ⟨14786904416965535924522363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9857936277977023949681575 14786904416965535924522363)
        ·
          refine ⟨22180356625448303886783545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14786904416965535924522363 22180356625448303886783545)
          ·
            refine ⟨16635267469086227915087659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22180356625448303886783545 16635267469086227915087659)
            ·
              refine ⟨24952901203629341872631489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16635267469086227915087659 24952901203629341872631489)
              ·
                refine ⟨18714675902722006404473617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24952901203629341872631489 18714675902722006404473617)
                ·
                  refine ⟨14036006927041504803355213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18714675902722006404473617 14036006927041504803355213)
                  ·
                    refine ⟨5263502597640564301258205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14036006927041504803355213 5263502597640564301258205)
                    ·
                      refine ⟨1973813474115211612971827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5263502597640564301258205 1973813474115211612971827)
                      ·
                        rfl

theorem cell23_3843988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3843988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3843988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3843988 prefixEnd_3843988 := by exact prefixLift 3843988
  have htrace : WordTrace (prefixWord ++ tailWord_3843988) baseStart_3843988 baseEnd_3843988 := by
    simpa [prefixWord, tailWord_3843988, baseEnd_3843988] using wordTrace_append hprefix tailTrace_3843988
  have hstable : (prefixWord ++ tailWord_3843988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3843988).length < 2 ^ (prefixWord ++ tailWord_3843988).sum := by decide
  have hdescent : baseEnd_3843988 < baseStart_3843988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3843988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844031 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 3]
def baseStart_3844031 : Nat := 118140960795 + 3844031 * 2 ^ 59
def prefixEnd_3844031 : Nat := 4983230072969 + 3 ^ 40 * 3844031 * 2
def baseEnd_3844031 : Nat := 1973835553783354944734129

theorem tailTrace_3844031 : CollatzResearch.WordTrace tailWord_3844031 prefixEnd_3844031 1973835553783354944734129 := by
  unfold tailWord_3844031
  simp only [CollatzResearch.WordTrace]
  refine ⟨140203328736739670072619947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93468885824493113381746631 140203328736739670072619947)
  ·
    refine ⟨210304993105109505108929921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140203328736739670072619947 210304993105109505108929921)
    ·
      refine ⟨157728744828832128831697441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210304993105109505108929921 157728744828832128831697441)
      ·
        refine ⟨118296558621624096623773081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157728744828832128831697441 118296558621624096623773081)
        ·
          refine ⟨88722418966218072467829811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118296558621624096623773081 88722418966218072467829811)
          ·
            refine ⟨133083628449327108701744717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88722418966218072467829811 133083628449327108701744717)
            ·
              refine ⟨49906360668497665763154269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133083628449327108701744717 49906360668497665763154269)
              ·
                refine ⟨18714885250686624661182851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49906360668497665763154269 18714885250686624661182851)
                ·
                  refine ⟨28072327876029936991774277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18714885250686624661182851 28072327876029936991774277)
                  ·
                    refine ⟨5263561476755613185957677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28072327876029936991774277 5263561476755613185957677)
                    ·
                      refine ⟨1973835553783354944734129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5263561476755613185957677 1973835553783354944734129)
                      ·
                        rfl

theorem cell23_3844031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_3844031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844031 prefixEnd_3844031 := by exact prefixLift 3844031
  have htrace : WordTrace (prefixWord ++ tailWord_3844031) baseStart_3844031 baseEnd_3844031 := by
    simpa [prefixWord, tailWord_3844031, baseEnd_3844031] using wordTrace_append hprefix tailTrace_3844031
  have hstable : (prefixWord ++ tailWord_3844031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844031).length < 2 ^ (prefixWord ++ tailWord_3844031).sum := by decide
  have hdescent : baseEnd_3844031 < baseStart_3844031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844088 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 1, 5, 2]
def baseStart_3844088 : Nat := 118140960795 + 3844088 * 2 ^ 59
def prefixEnd_3844088 : Nat := 4983230072969 + 3 ^ 40 * 3844088 * 2
def baseEnd_3844088 : Nat := 1973864822180661221721367

theorem tailTrace_3844088 : CollatzResearch.WordTrace tailWord_3844088 prefixEnd_3844088 1973864822180661221721367 := by
  unfold tailWord_3844088
  simp only [CollatzResearch.WordTrace]
  refine ⟨70102703848766584403722459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93470271798355445871629945 70102703848766584403722459)
  ·
    refine ⟨105154055773149876605583689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70102703848766584403722459 105154055773149876605583689)
    ·
      refine ⟨78865541829862407454187767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105154055773149876605583689 78865541829862407454187767)
      ·
        refine ⟨118298312744793611181281651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78865541829862407454187767 118298312744793611181281651)
        ·
          refine ⟨177447469117190416771922477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118298312744793611181281651 177447469117190416771922477)
          ·
            refine ⟨66542800918946406289470929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177447469117190416771922477 66542800918946406289470929)
            ·
              refine ⟨49907100689209804717103197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66542800918946406289470929 49907100689209804717103197)
              ·
                refine ⟨18715162758453676768913699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49907100689209804717103197 18715162758453676768913699)
                ·
                  refine ⟨28072744137680515153370549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18715162758453676768913699 28072744137680515153370549)
                  ·
                    refine ⟨2631819762907548295628489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28072744137680515153370549 2631819762907548295628489)
                    ·
                      refine ⟨1973864822180661221721367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631819762907548295628489 1973864822180661221721367)
                      ·
                        rfl

theorem cell23_3844088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_3844088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844088 prefixEnd_3844088 := by exact prefixLift 3844088
  have htrace : WordTrace (prefixWord ++ tailWord_3844088) baseStart_3844088 baseEnd_3844088 := by
    simpa [prefixWord, tailWord_3844088, baseEnd_3844088] using wordTrace_append hprefix tailTrace_3844088
  have hstable : (prefixWord ++ tailWord_3844088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844088).length < 2 ^ (prefixWord ++ tailWord_3844088).sum := by decide
  have hdescent : baseEnd_3844088 < baseStart_3844088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844106 : List Nat := [3, 1, 2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_3844106 : Nat := 118140960795 + 3844106 * 2 ^ 59
def prefixEnd_3844106 : Nat := 4983230072969 + 3 ^ 40 * 3844106 * 2
def baseEnd_3844106 : Nat := 657958021610814050432095

theorem tailTrace_3844106 : CollatzResearch.WordTrace tailWord_3844106 prefixEnd_3844106 657958021610814050432095 := by
  unfold tailWord_3844106
  simp only [CollatzResearch.WordTrace]
  refine ⟨35051516052866989470400043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93470709474311971921066781 35051516052866989470400043)
  ·
    refine ⟨52577274079300484205600065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35051516052866989470400043 52577274079300484205600065)
    ·
      refine ⟨39432955559475363154200049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52577274079300484205600065 39432955559475363154200049)
      ·
        refine ⟨29574716669606522365650037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39432955559475363154200049 29574716669606522365650037)
        ·
          refine ⟨2772629687775611471779691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29574716669606522365650037 2772629687775611471779691)
          ·
            refine ⟨4158944531663417207669537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772629687775611471779691 4158944531663417207669537)
            ·
              refine ⟨3119208398747562905752153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158944531663417207669537 3119208398747562905752153)
              ·
                refine ⟨2339406299060672179314115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119208398747562905752153 2339406299060672179314115)
                ·
                  refine ⟨3509109448591008268971173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339406299060672179314115 3509109448591008268971173)
                  ·
                    refine ⟨657958021610814050432095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3509109448591008268971173 657958021610814050432095)
                    ·
                      rfl

theorem cell23_3844106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_3844106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844106 prefixEnd_3844106 := by exact prefixLift 3844106
  have htrace : WordTrace (prefixWord ++ tailWord_3844106) baseStart_3844106 baseEnd_3844106 := by
    simpa [prefixWord, tailWord_3844106, baseEnd_3844106] using wordTrace_append hprefix tailTrace_3844106
  have hstable : (prefixWord ++ tailWord_3844106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844106).length < 2 ^ (prefixWord ++ tailWord_3844106).sum := by decide
  have hdescent : baseEnd_3844106 < baseStart_3844106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844121 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_3844121 : Nat := 118140960795 + 3844121 * 2 ^ 59
def prefixEnd_3844121 : Nat := 4983230072969 + 3 ^ 40 * 3844121 * 2
def baseEnd_3844121 : Nat := 1973881767042259592608715

theorem tailTrace_3844121 : CollatzResearch.WordTrace tailWord_3844121 prefixEnd_3844121 1973881767042259592608715 := by
  unfold tailWord_3844121
  simp only [CollatzResearch.WordTrace]
  refine ⟨140206611306413615443396217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93471074204275743628930811 140206611306413615443396217)
  ·
    refine ⟨105154958479810211582547163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140206611306413615443396217 105154958479810211582547163)
    ·
      refine ⟨157732437719715317373820745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105154958479810211582547163 157732437719715317373820745)
      ·
        refine ⟨118299328289786488030365559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157732437719715317373820745 118299328289786488030365559)
        ·
          refine ⟨177448992434679732045548339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118299328289786488030365559 177448992434679732045548339)
          ·
            refine ⟨266173488652019598068322509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177448992434679732045548339 266173488652019598068322509)
            ·
              refine ⟨99815058244507349275620941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266173488652019598068322509 99815058244507349275620941)
              ·
                refine ⟨37430646841690255978357853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99815058244507349275620941 37430646841690255978357853)
                ·
                  refine ⟨14036492565633845991884195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37430646841690255978357853 14036492565633845991884195)
                  ·
                    refine ⟨21054738848450768987826293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14036492565633845991884195 21054738848450768987826293)
                    ·
                      refine ⟨1973881767042259592608715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21054738848450768987826293 1973881767042259592608715)
                      ·
                        rfl

theorem cell23_3844121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_3844121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844121 prefixEnd_3844121 := by exact prefixLift 3844121
  have htrace : WordTrace (prefixWord ++ tailWord_3844121) baseStart_3844121 baseEnd_3844121 := by
    simpa [prefixWord, tailWord_3844121, baseEnd_3844121] using wordTrace_append hprefix tailTrace_3844121
  have hstable : (prefixWord ++ tailWord_3844121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844121).length < 2 ^ (prefixWord ++ tailWord_3844121).sum := by decide
  have hdescent : baseEnd_3844121 < baseStart_3844121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844182 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3844182 : Nat := 118140960795 + 3844182 * 2 ^ 59
def prefixEnd_3844182 : Nat := 4983230072969 + 3 ^ 40 * 3844182 * 2
def baseEnd_3844182 : Nat := 1973913089362183853945935

theorem tailTrace_3844182 : CollatzResearch.WordTrace tailWord_3844182 prefixEnd_3844182 1973913089362183853945935 := by
  unfold tailWord_3844182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763052259949538928835425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93472557439461748574244533 8763052259949538928835425)
  ·
    refine ⟨6572289194962154196626569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8763052259949538928835425 6572289194962154196626569)
    ·
      refine ⟨4929216896221615647469927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6572289194962154196626569 4929216896221615647469927)
      ·
        refine ⟨7393825344332423471204891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4929216896221615647469927 7393825344332423471204891)
        ·
          refine ⟨11090738016498635206807337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393825344332423471204891 11090738016498635206807337)
          ·
            refine ⟨8318053512373976405105503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11090738016498635206807337 8318053512373976405105503)
            ·
              refine ⟨12477080268560964607658255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318053512373976405105503 12477080268560964607658255)
              ·
                refine ⟨18715620402841446911487383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12477080268560964607658255 18715620402841446911487383)
                ·
                  refine ⟨28073430604262170367231075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18715620402841446911487383 28073430604262170367231075)
                  ·
                    refine ⟨42110145906393255550846613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28073430604262170367231075 42110145906393255550846613)
                    ·
                      refine ⟨1973913089362183853945935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42110145906393255550846613 1973913089362183853945935)
                      ·
                        rfl

theorem cell23_3844182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3844182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844182 prefixEnd_3844182 := by exact prefixLift 3844182
  have htrace : WordTrace (prefixWord ++ tailWord_3844182) baseStart_3844182 baseEnd_3844182 := by
    simpa [prefixWord, tailWord_3844182, baseEnd_3844182] using wordTrace_append hprefix tailTrace_3844182
  have hstable : (prefixWord ++ tailWord_3844182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844182).length < 2 ^ (prefixWord ++ tailWord_3844182).sum := by decide
  have hdescent : baseEnd_3844182 < baseStart_3844182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844189 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3844189 : Nat := 118140960795 + 3844189 * 2 ^ 59
def prefixEnd_3844189 : Nat := 4983230072969 + 3 ^ 40 * 3844189 * 2
def baseEnd_3844189 : Nat := 1973916683726765326558403

theorem tailTrace_3844189 : CollatzResearch.WordTrace tailWord_3844189 prefixEnd_3844189 1973916683726765326558403 := by
  unfold tailWord_3844189
  simp only [CollatzResearch.WordTrace]
  refine ⟨140209091470167263056871621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93472727646778175371247747 140209091470167263056871621)
  ·
    refine ⟨26289204650656361823163429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140209091470167263056871621 26289204650656361823163429)
    ·
      refine ⟨4929225871998067841843143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26289204650656361823163429 4929225871998067841843143)
      ·
        refine ⟨7393838807997101762764715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4929225871998067841843143 7393838807997101762764715)
        ·
          refine ⟨11090758211995652644147073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393838807997101762764715 11090758211995652644147073)
          ·
            refine ⟨8318068658996739483110305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11090758211995652644147073 8318068658996739483110305)
            ·
              refine ⟨6238551494247554612332729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318068658996739483110305 6238551494247554612332729)
              ·
                refine ⟨4678913620685665959249547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6238551494247554612332729 4678913620685665959249547)
                ·
                  refine ⟨7018370431028498938874321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678913620685665959249547 7018370431028498938874321)
                  ·
                    refine ⟨5263777823271374204155741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7018370431028498938874321 5263777823271374204155741)
                    ·
                      refine ⟨1973916683726765326558403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5263777823271374204155741 1973916683726765326558403)
                      ·
                        rfl

theorem cell23_3844189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3844189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844189 prefixEnd_3844189 := by exact prefixLift 3844189
  have htrace : WordTrace (prefixWord ++ tailWord_3844189) baseStart_3844189 baseEnd_3844189 := by
    simpa [prefixWord, tailWord_3844189, baseEnd_3844189] using wordTrace_append hprefix tailTrace_3844189
  have hstable : (prefixWord ++ tailWord_3844189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844189).length < 2 ^ (prefixWord ++ tailWord_3844189).sum := by decide
  have hdescent : baseEnd_3844189 < baseStart_3844189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844191 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_3844191 : Nat := 118140960795 + 3844191 * 2 ^ 59
def prefixEnd_3844191 : Nat := 4983230072969 + 3 ^ 40 * 3844191 * 2
def baseEnd_3844191 : Nat := 1973917710688074318733393

theorem tailTrace_3844191 : CollatzResearch.WordTrace tailWord_3844191 prefixEnd_3844191 1973917710688074318733393 := by
  unfold tailWord_3844191
  simp only [CollatzResearch.WordTrace]
  refine ⟨140209164416160017398444427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93472776277440011598962951 140209164416160017398444427)
  ·
    refine ⟨210313746624240026097666641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140209164416160017398444427 210313746624240026097666641)
    ·
      refine ⟨157735309968180019573249981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210313746624240026097666641 157735309968180019573249981)
      ·
        refine ⟨59150741238067507339968743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157735309968180019573249981 59150741238067507339968743)
        ·
          refine ⟨88726111857101261009953115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59150741238067507339968743 88726111857101261009953115)
          ·
            refine ⟨133089167785651891514929673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88726111857101261009953115 133089167785651891514929673)
            ·
              refine ⟨99816875839238918636197255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133089167785651891514929673 99816875839238918636197255)
              ·
                refine ⟨149725313758858377954295883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99816875839238918636197255 149725313758858377954295883)
                ·
                  refine ⟨224587970638287566931443825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149725313758858377954295883 224587970638287566931443825)
                  ·
                    refine ⟨168440977978715675198582869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 224587970638287566931443825 168440977978715675198582869)
                    ·
                      refine ⟨1973917710688074318733393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 168440977978715675198582869 1973917710688074318733393)
                      ·
                        rfl

theorem cell23_3844191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_3844191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844191 prefixEnd_3844191 := by exact prefixLift 3844191
  have htrace : WordTrace (prefixWord ++ tailWord_3844191) baseStart_3844191 baseEnd_3844191 := by
    simpa [prefixWord, tailWord_3844191, baseEnd_3844191] using wordTrace_append hprefix tailTrace_3844191
  have hstable : (prefixWord ++ tailWord_3844191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844191).length < 2 ^ (prefixWord ++ tailWord_3844191).sum := by decide
  have hdescent : baseEnd_3844191 < baseStart_3844191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844195 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 3, 3, 2]
def baseStart_3844195 : Nat := 118140960795 + 3844195 * 2 ^ 59
def prefixEnd_3844195 : Nat := 4983230072969 + 3 ^ 40 * 3844195 * 2
def baseEnd_3844195 : Nat := 1973919764610692303083375

theorem tailTrace_3844195 : CollatzResearch.WordTrace tailWord_3844195 prefixEnd_3844195 1973919764610692303083375 := by
  unfold tailWord_3844195
  simp only [CollatzResearch.WordTrace]
  refine ⟨140209310308145526081590039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93472873538763684054393359 140209310308145526081590039)
  ·
    refine ⟨210313965462218289122385059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140209310308145526081590039 210313965462218289122385059)
    ·
      refine ⟨315470948193327433683577589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210313965462218289122385059 315470948193327433683577589)
      ·
        refine ⟨29575401393124446907835399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315470948193327433683577589 29575401393124446907835399)
        ·
          refine ⟨44363102089686670361753099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29575401393124446907835399 44363102089686670361753099)
          ·
            refine ⟨66544653134530005542629649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44363102089686670361753099 66544653134530005542629649)
            ·
              refine ⟨49908489850897504156972237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66544653134530005542629649 49908489850897504156972237)
              ·
                refine ⟨18715683694086564058864589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49908489850897504156972237 18715683694086564058864589)
                ·
                  refine ⟨7018381385282461522074221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18715683694086564058864589 7018381385282461522074221)
                  ·
                    refine ⟨2631893019480923070777833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7018381385282461522074221 2631893019480923070777833)
                    ·
                      refine ⟨1973919764610692303083375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631893019480923070777833 1973919764610692303083375)
                      ·
                        rfl

theorem cell23_3844195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_3844195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844195 prefixEnd_3844195 := by exact prefixLift 3844195
  have htrace : WordTrace (prefixWord ++ tailWord_3844195) baseStart_3844195 baseEnd_3844195 := by
    simpa [prefixWord, tailWord_3844195, baseEnd_3844195] using wordTrace_append hprefix tailTrace_3844195
  have hstable : (prefixWord ++ tailWord_3844195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844195).length < 2 ^ (prefixWord ++ tailWord_3844195).sum := by decide
  have hdescent : baseEnd_3844195 < baseStart_3844195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844228 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3844228 : Nat := 118140960795 + 3844228 * 2 ^ 59
def prefixEnd_3844228 : Nat := 4983230072969 + 3 ^ 40 * 3844228 * 2
def baseEnd_3844228 : Nat := 1973936709472290673970723

theorem tailTrace_3844228 : CollatzResearch.WordTrace tailWord_3844228 prefixEnd_3844228 1973936709472290673970723 := by
  unfold tailWord_3844228
  simp only [CollatzResearch.WordTrace]
  refine ⟨70105256958512986358770669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93473675944683981811694225 70105256958512986358770669)
  ·
    refine ⟨26289471359442369884539001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70105256958512986358770669 26289471359442369884539001)
    ·
      refine ⟨19717103519581777413404251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26289471359442369884539001 19717103519581777413404251)
      ·
        refine ⟨29575655279372666120106377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19717103519581777413404251 29575655279372666120106377)
        ·
          refine ⟨22181741459529499590079783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29575655279372666120106377 22181741459529499590079783)
          ·
            refine ⟨33272612189294249385119675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22181741459529499590079783 33272612189294249385119675)
            ·
              refine ⟨49908918283941374077679513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33272612189294249385119675 49908918283941374077679513)
              ·
                refine ⟨37431688712956030558259635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49908918283941374077679513 37431688712956030558259635)
                ·
                  refine ⟨56147533069434045837389453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37431688712956030558259635 56147533069434045837389453)
                  ·
                    refine ⟨21055324901037767189021045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56147533069434045837389453 21055324901037767189021045)
                    ·
                      refine ⟨1973936709472290673970723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21055324901037767189021045 1973936709472290673970723)
                      ·
                        rfl

theorem cell23_3844228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3844228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844228 prefixEnd_3844228 := by exact prefixLift 3844228
  have htrace : WordTrace (prefixWord ++ tailWord_3844228) baseStart_3844228 baseEnd_3844228 := by
    simpa [prefixWord, tailWord_3844228, baseEnd_3844228] using wordTrace_append hprefix tailTrace_3844228
  have hstable : (prefixWord ++ tailWord_3844228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844228).length < 2 ^ (prefixWord ++ tailWord_3844228).sum := by decide
  have hdescent : baseEnd_3844228 < baseStart_3844228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844242 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_3844242 : Nat := 118140960795 + 3844242 * 2 ^ 59
def prefixEnd_3844242 : Nat := 4983230072969 + 3 ^ 40 * 3844242 * 2
def baseEnd_3844242 : Nat := 1973943898201453619195659

theorem tailTrace_3844242 : CollatzResearch.WordTrace tailWord_3844242 prefixEnd_3844242 1973943898201453619195659 := by
  unfold tailWord_3844242
  simp only [CollatzResearch.WordTrace]
  refine ⟨35052756134743813277137745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93474016359316835405700653 35052756134743813277137745)
  ·
    refine ⟨26289567101057859957853309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35052756134743813277137745 26289567101057859957853309)
    ·
      refine ⟨9858587662896697484194991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26289567101057859957853309 9858587662896697484194991)
      ·
        refine ⟨14787881494345046226292487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9858587662896697484194991 14787881494345046226292487)
        ·
          refine ⟨22181822241517569339438731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14787881494345046226292487 22181822241517569339438731)
          ·
            refine ⟨33272733362276354009158097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22181822241517569339438731 33272733362276354009158097)
            ·
              refine ⟨24954550021707265506868573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33272733362276354009158097 24954550021707265506868573)
              ·
                refine ⟨9357956258140224565075715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24954550021707265506868573 9357956258140224565075715)
                ·
                  refine ⟨14036934387210336847613573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9357956258140224565075715 14036934387210336847613573)
                  ·
                    refine ⟨2631925197601938158927545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14036934387210336847613573 2631925197601938158927545)
                    ·
                      refine ⟨1973943898201453619195659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631925197601938158927545 1973943898201453619195659)
                      ·
                        rfl

theorem cell23_3844242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_3844242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844242 prefixEnd_3844242 := by exact prefixLift 3844242
  have htrace : WordTrace (prefixWord ++ tailWord_3844242) baseStart_3844242 baseEnd_3844242 := by
    simpa [prefixWord, tailWord_3844242, baseEnd_3844242] using wordTrace_append hprefix tailTrace_3844242
  have hstable : (prefixWord ++ tailWord_3844242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844242).length < 2 ^ (prefixWord ++ tailWord_3844242).sum := by decide
  have hdescent : baseEnd_3844242 < baseStart_3844242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844282 : List Nat := [3, 1, 1, 1, 2, 2, 6, 2, 5]
def baseStart_3844282 : Nat := 118140960795 + 3844282 * 2 ^ 59
def prefixEnd_3844282 : Nat := 4983230072969 + 3 ^ 40 * 3844282 * 2
def baseEnd_3844282 : Nat := 219329381936403718077275

theorem tailTrace_3844282 : CollatzResearch.WordTrace tailWord_3844282 prefixEnd_3844282 219329381936403718077275 := by
  unfold tailWord_3844282
  simp only [CollatzResearch.WordTrace]
  refine ⟨35053120864707584985001775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93474988972553559960004733 35053120864707584985001775)
  ·
    refine ⟨52579681297061377477502663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35053120864707584985001775 52579681297061377477502663)
    ·
      refine ⟨78869521945592066216253995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52579681297061377477502663 78869521945592066216253995)
      ·
        refine ⟨118304282918388099324380993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78869521945592066216253995 118304282918388099324380993)
        ·
          refine ⟨88728212188791074493285745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118304282918388099324380993 88728212188791074493285745)
          ·
            refine ⟨66546159141593305869964309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88728212188791074493285745 66546159141593305869964309)
            ·
              refine ⟨3119351209762186212654577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66546159141593305869964309 3119351209762186212654577)
              ·
                refine ⟨2339513407321639659490933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119351209762186212654577 2339513407321639659490933)
                ·
                  refine ⟨219329381936403718077275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2339513407321639659490933 219329381936403718077275)
                  ·
                    rfl

theorem cell23_3844282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_3844282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844282 prefixEnd_3844282 := by exact prefixLift 3844282
  have htrace : WordTrace (prefixWord ++ tailWord_3844282) baseStart_3844282 baseEnd_3844282 := by
    simpa [prefixWord, tailWord_3844282, baseEnd_3844282] using wordTrace_append hprefix tailTrace_3844282
  have hstable : (prefixWord ++ tailWord_3844282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844282).length < 2 ^ (prefixWord ++ tailWord_3844282).sum := by decide
  have hdescent : baseEnd_3844282 < baseStart_3844282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844292 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3844292 : Nat := 118140960795 + 3844292 * 2 ^ 59
def prefixEnd_3844292 : Nat := 4983230072969 + 3 ^ 40 * 3844292 * 2
def baseEnd_3844292 : Nat := 1973969572234178423570429

theorem tailTrace_3844292 : CollatzResearch.WordTrace tailWord_3844292 prefixEnd_3844292 1973969572234178423570429 := by
  unfold tailWord_3844292
  simp only [CollatzResearch.WordTrace]
  refine ⟨70106424094397055823935565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93475232125862741098580753 70106424094397055823935565)
  ·
    refine ⟨26289909035398895933975837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70106424094397055823935565 26289909035398895933975837)
    ·
      refine ⟨9858715888274585975240939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26289909035398895933975837 9858715888274585975240939)
      ·
        refine ⟨14788073832411878962861409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9858715888274585975240939 14788073832411878962861409)
        ·
          refine ⟨11091055374308909222146057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14788073832411878962861409 11091055374308909222146057)
          ·
            refine ⟨8318291530731681916609543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11091055374308909222146057 8318291530731681916609543)
            ·
              refine ⟨12477437296097522874914315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318291530731681916609543 12477437296097522874914315)
              ·
                refine ⟨18716155944146284312371473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12477437296097522874914315 18716155944146284312371473)
                ·
                  refine ⟨14037116958109713234278605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18716155944146284312371473 14037116958109713234278605)
                  ·
                    refine ⟨5263918859291142462854477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14037116958109713234278605 5263918859291142462854477)
                    ·
                      refine ⟨1973969572234178423570429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5263918859291142462854477 1973969572234178423570429)
                      ·
                        rfl

theorem cell23_3844292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3844292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844292 prefixEnd_3844292 := by exact prefixLift 3844292
  have htrace : WordTrace (prefixWord ++ tailWord_3844292) baseStart_3844292 baseEnd_3844292 := by
    simpa [prefixWord, tailWord_3844292, baseEnd_3844292] using wordTrace_append hprefix tailTrace_3844292
  have hstable : (prefixWord ++ tailWord_3844292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844292).length < 2 ^ (prefixWord ++ tailWord_3844292).sum := by decide
  have hdescent : baseEnd_3844292 < baseStart_3844292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844312 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 2, 5]
def baseStart_3844312 : Nat := 118140960795 + 3844312 * 2 ^ 59
def prefixEnd_3844312 : Nat := 4983230072969 + 3 ^ 40 * 3844312 * 2
def baseEnd_3844312 : Nat := 657993280615756115106779

theorem tailTrace_3844312 : CollatzResearch.WordTrace tailWord_3844312 prefixEnd_3844312 657993280615756115106779 := by
  unfold tailWord_3844312
  simp only [CollatzResearch.WordTrace]
  refine ⟨70106788824360827531799595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93475718432481103375732793 70106788824360827531799595)
  ·
    refine ⟨105160183236541241297699393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70106788824360827531799595 105160183236541241297699393)
    ·
      refine ⟨78870137427405930973274545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105160183236541241297699393 78870137427405930973274545)
      ·
        refine ⟨59152603070554448229955909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78870137427405930973274545 59152603070554448229955909)
        ·
          refine ⟨11091113075728959043116733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59152603070554448229955909 11091113075728959043116733)
          ·
            refine ⟨4159167403398359641168775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11091113075728959043116733 4159167403398359641168775)
            ·
              refine ⟨6238751105097539461753163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159167403398359641168775 6238751105097539461753163)
              ·
                refine ⟨9358126657646309192629745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238751105097539461753163 9358126657646309192629745)
                ·
                  refine ⟨7018594993234731894472309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9358126657646309192629745 7018594993234731894472309)
                  ·
                    refine ⟨657993280615756115106779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7018594993234731894472309 657993280615756115106779)
                    ·
                      rfl

theorem cell23_3844312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_3844312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844312 prefixEnd_3844312 := by exact prefixLift 3844312
  have htrace : WordTrace (prefixWord ++ tailWord_3844312) baseStart_3844312 baseEnd_3844312 := by
    simpa [prefixWord, tailWord_3844312, baseEnd_3844312] using wordTrace_append hprefix tailTrace_3844312
  have hstable : (prefixWord ++ tailWord_3844312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844312).length < 2 ^ (prefixWord ++ tailWord_3844312).sum := by decide
  have hdescent : baseEnd_3844312 < baseStart_3844312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844315 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 4, 4, 2]
def baseStart_3844315 : Nat := 118140960795 + 3844315 * 2 ^ 59
def prefixEnd_3844315 : Nat := 4983230072969 + 3 ^ 40 * 3844315 * 2
def baseEnd_3844315 : Nat := 1973981382289231833582823

theorem tailTrace_3844315 : CollatzResearch.WordTrace tailWord_3844315 prefixEnd_3844315 1973981382289231833582823 := by
  unfold tailWord_3844315
  simp only [CollatzResearch.WordTrace]
  refine ⟨140213687067710786575958399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93475791378473857717305599 140213687067710786575958399)
  ·
    refine ⟨210320530601566179863937599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140213687067710786575958399 210320530601566179863937599)
    ·
      refine ⟨315480795902349269795906399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210320530601566179863937599 315480795902349269795906399)
      ·
        refine ⟨473221193853523904693859599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315480795902349269795906399 473221193853523904693859599)
        ·
          refine ⟨709831790780285857040789399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473221193853523904693859599 709831790780285857040789399)
          ·
            refine ⟨1064747686170428785561184099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709831790780285857040789399 1064747686170428785561184099)
            ·
              refine ⟨1597121529255643178341776149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064747686170428785561184099 1597121529255643178341776149)
              ·
                refine ⟨74865071683858273984770757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1597121529255643178341776149 74865071683858273984770757)
                ·
                  refine ⟨14037200940723426372144517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74865071683858273984770757 14037200940723426372144517)
                  ·
                    refine ⟨2631975176385642444777097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14037200940723426372144517 2631975176385642444777097)
                    ·
                      refine ⟨1973981382289231833582823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2631975176385642444777097 1973981382289231833582823)
                      ·
                        rfl

theorem cell23_3844315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 4, 2].length) (baseStart_3844315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844315 prefixEnd_3844315 := by exact prefixLift 3844315
  have htrace : WordTrace (prefixWord ++ tailWord_3844315) baseStart_3844315 baseEnd_3844315 := by
    simpa [prefixWord, tailWord_3844315, baseEnd_3844315] using wordTrace_append hprefix tailTrace_3844315
  have hstable : (prefixWord ++ tailWord_3844315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844315).length < 2 ^ (prefixWord ++ tailWord_3844315).sum := by decide
  have hdescent : baseEnd_3844315 < baseStart_3844315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844316 : List Nat := [2, 2, 5, 2, 1, 1, 2, 3, 5]
def baseStart_3844316 : Nat := 118140960795 + 3844316 * 2 ^ 59
def prefixEnd_3844316 : Nat := 4983230072969 + 3 ^ 40 * 3844316 * 2
def baseEnd_3844316 : Nat := 219331321752209592185591

theorem tailTrace_3844316 : CollatzResearch.WordTrace tailWord_3844316 prefixEnd_3844316 219331321752209592185591 := by
  unfold tailWord_3844316
  simp only [CollatzResearch.WordTrace]
  refine ⟨70106861770353581873372401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93475815693804775831163201 70106861770353581873372401)
  ·
    refine ⟨52580146327765186405029301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70106861770353581873372401 52580146327765186405029301)
    ·
      refine ⟨4929388718227986225471497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52580146327765186405029301 4929388718227986225471497)
      ·
        refine ⟨3697041538670989669103623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4929388718227986225471497 3697041538670989669103623)
        ·
          refine ⟨5545562308006484503655435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697041538670989669103623 5545562308006484503655435)
          ·
            refine ⟨8318343462009726755483153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545562308006484503655435 8318343462009726755483153)
            ·
              refine ⟨6238757596507295066612365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318343462009726755483153 6238757596507295066612365)
              ·
                refine ⟨2339534098690235649979637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6238757596507295066612365 2339534098690235649979637)
                ·
                  refine ⟨219331321752209592185591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2339534098690235649979637 219331321752209592185591)
                  ·
                    rfl

theorem cell23_3844316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_3844316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844316 prefixEnd_3844316 := by exact prefixLift 3844316
  have htrace : WordTrace (prefixWord ++ tailWord_3844316) baseStart_3844316 baseEnd_3844316 := by
    simpa [prefixWord, tailWord_3844316, baseEnd_3844316] using wordTrace_append hprefix tailTrace_3844316
  have hstable : (prefixWord ++ tailWord_3844316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844316).length < 2 ^ (prefixWord ++ tailWord_3844316).sum := by decide
  have hdescent : baseEnd_3844316 < baseStart_3844316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844342 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_3844342 : Nat := 118140960795 + 3844342 * 2 ^ 59
def prefixEnd_3844342 : Nat := 4983230072969 + 3 ^ 40 * 3844342 * 2
def baseEnd_3844342 : Nat := 657998415422301075981733

theorem tailTrace_3844342 : CollatzResearch.WordTrace tailWord_3844342 prefixEnd_3844342 657998415422301075981733 := by
  unfold tailWord_3844342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763416989913310636699455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93476447892408646791460853 8763416989913310636699455)
  ·
    refine ⟨13145125484869965955049183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8763416989913310636699455 13145125484869965955049183)
    ·
      refine ⟨19717688227304948932573775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13145125484869965955049183 19717688227304948932573775)
      ·
        refine ⟨29576532340957423398860663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19717688227304948932573775 29576532340957423398860663)
        ·
          refine ⟨44364798511436135098290995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29576532340957423398860663 44364798511436135098290995)
          ·
            refine ⟨66547197767154202647436493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44364798511436135098290995 66547197767154202647436493)
            ·
              refine ⟨24955199162682825992788685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66547197767154202647436493 24955199162682825992788685)
              ·
                refine ⟨9358199686006059747295757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24955199162682825992788685 9358199686006059747295757)
                ·
                  refine ⟨3509324882252272405235909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9358199686006059747295757 3509324882252272405235909)
                  ·
                    refine ⟨657998415422301075981733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3509324882252272405235909 657998415422301075981733)
                    ·
                      rfl

theorem cell23_3844342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_3844342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844342 prefixEnd_3844342 := by exact prefixLift 3844342
  have htrace : WordTrace (prefixWord ++ tailWord_3844342) baseStart_3844342 baseEnd_3844342 := by
    simpa [prefixWord, tailWord_3844342, baseEnd_3844342] using wordTrace_append hprefix tailTrace_3844342
  have hstable : (prefixWord ++ tailWord_3844342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844342).length < 2 ^ (prefixWord ++ tailWord_3844342).sum := by decide
  have hdescent : baseEnd_3844342 < baseStart_3844342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844399 : List Nat := [1, 1, 2, 1, 2, 1, 4, 6, 1, 1, 3]
def baseStart_3844399 : Nat := 118140960795 + 3844399 * 2 ^ 59
def prefixEnd_3844399 : Nat := 4983230072969 + 3 ^ 40 * 3844399 * 2
def baseEnd_3844399 : Nat := 1974024514664209504932437

theorem tailTrace_3844399 : CollatzResearch.WordTrace tailWord_3844399 prefixEnd_3844399 1974024514664209504932437 := by
  unfold tailWord_3844399
  simp only [CollatzResearch.WordTrace]
  refine ⟨140216750799406468922016251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93477833866270979281344167 140216750799406468922016251)
  ·
    refine ⟨210325126199109703383024377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140216750799406468922016251 210325126199109703383024377)
    ·
      refine ⟨157743844649332277537268283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210325126199109703383024377 157743844649332277537268283)
      ·
        refine ⟨236615766973998416305902425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157743844649332277537268283 236615766973998416305902425)
        ·
          refine ⟨177461825230498812229426819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236615766973998416305902425 177461825230498812229426819)
          ·
            refine ⟨266192737845748218344140229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177461825230498812229426819 266192737845748218344140229)
            ·
              refine ⟨49911138346077790939526293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266192737845748218344140229 49911138346077790939526293)
              ·
                refine ⟨2339584609972396450290295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49911138346077790939526293 2339584609972396450290295)
                ·
                  refine ⟨3509376914958594675435443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339584609972396450290295 3509376914958594675435443)
                  ·
                    refine ⟨5264065372437892013153165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3509376914958594675435443 5264065372437892013153165)
                    ·
                      refine ⟨1974024514664209504932437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5264065372437892013153165 1974024514664209504932437)
                      ·
                        rfl

theorem cell23_3844399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 1, 1, 3].length) (baseStart_3844399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844399 prefixEnd_3844399 := by exact prefixLift 3844399
  have htrace : WordTrace (prefixWord ++ tailWord_3844399) baseStart_3844399 baseEnd_3844399 := by
    simpa [prefixWord, tailWord_3844399, baseEnd_3844399] using wordTrace_append hprefix tailTrace_3844399
  have hstable : (prefixWord ++ tailWord_3844399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844399).length < 2 ^ (prefixWord ++ tailWord_3844399).sum := by decide
  have hdescent : baseEnd_3844399 < baseStart_3844399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844415 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 1, 6]
def baseStart_3844415 : Nat := 118140960795 + 3844415 * 2 ^ 59
def prefixEnd_3844415 : Nat := 4983230072969 + 3 ^ 40 * 3844415 * 2
def baseEnd_3844415 : Nat := 658010910118227147444121

theorem tailTrace_3844415 : CollatzResearch.WordTrace tailWord_3844415 prefixEnd_3844415 658010910118227147444121 := by
  unfold tailWord_3844415
  simp only [CollatzResearch.WordTrace]
  refine ⟨140217334367348503654598699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93478222911565669103065799 140217334367348503654598699)
  ·
    refine ⟨210326001551022755481898049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140217334367348503654598699 210326001551022755481898049)
    ·
      refine ⟨157744501163267066611423537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210326001551022755481898049 157744501163267066611423537)
      ·
        refine ⟨118308375872450299958567653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157744501163267066611423537 118308375872450299958567653)
        ·
          refine ⟨22182820476084431242231435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118308375872450299958567653 22182820476084431242231435)
          ·
            refine ⟨33274230714126646863347153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22182820476084431242231435 33274230714126646863347153)
            ·
              refine ⟨24955673035594985147510365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33274230714126646863347153 24955673035594985147510365)
              ·
                refine ⟨9358377388348119430316387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24955673035594985147510365 9358377388348119430316387)
                ·
                  refine ⟨14037566082522179145474581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9358377388348119430316387 14037566082522179145474581)
                  ·
                    refine ⟨658010910118227147444121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14037566082522179145474581 658010910118227147444121)
                    ·
                      rfl

theorem cell23_3844415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_3844415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844415 prefixEnd_3844415 := by exact prefixLift 3844415
  have htrace : WordTrace (prefixWord ++ tailWord_3844415) baseStart_3844415 baseEnd_3844415 := by
    simpa [prefixWord, tailWord_3844415, baseEnd_3844415] using wordTrace_append hprefix tailTrace_3844415
  have hstable : (prefixWord ++ tailWord_3844415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844415).length < 2 ^ (prefixWord ++ tailWord_3844415).sum := by decide
  have hdescent : baseEnd_3844415 < baseStart_3844415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844439 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 1, 1, 4]
def baseStart_3844439 : Nat := 118140960795 + 3844439 * 2 ^ 59
def prefixEnd_3844439 : Nat := 4983230072969 + 3 ^ 40 * 3844439 * 2
def baseEnd_3844439 : Nat := 1974045053890389348432253

theorem tailTrace_3844439 : CollatzResearch.WordTrace tailWord_3844439 prefixEnd_3844439 1974045053890389348432253 := by
  unfold tailWord_3844439
  simp only [CollatzResearch.WordTrace]
  refine ⟨140218209719261555753472371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93478806479507703835648247 140218209719261555753472371)
  ·
    refine ⟨210327314578892333630208557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140218209719261555753472371 210327314578892333630208557)
    ·
      refine ⟨78872742967084625111328209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210327314578892333630208557 78872742967084625111328209)
      ·
        refine ⟨59154557225313468833496157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78872742967084625111328209 59154557225313468833496157)
        ·
          refine ⟨22182958959492550812561059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59154557225313468833496157 22182958959492550812561059)
          ·
            refine ⟨33274438439238826218841589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22182958959492550812561059 33274438439238826218841589)
            ·
              refine ⟨3119478603678639958016399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33274438439238826218841589 3119478603678639958016399)
              ·
                refine ⟨4679217905517959937024599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119478603678639958016399 4679217905517959937024599)
                ·
                  refine ⟨7018826858276939905536899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679217905517959937024599 7018826858276939905536899)
                  ·
                    refine ⟨10528240287415409858305349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7018826858276939905536899 10528240287415409858305349)
                    ·
                      refine ⟨1974045053890389348432253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10528240287415409858305349 1974045053890389348432253)
                      ·
                        rfl

theorem cell23_3844439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_3844439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844439 prefixEnd_3844439 := by exact prefixLift 3844439
  have htrace : WordTrace (prefixWord ++ tailWord_3844439) baseStart_3844439 baseEnd_3844439 := by
    simpa [prefixWord, tailWord_3844439, baseEnd_3844439] using wordTrace_append hprefix tailTrace_3844439
  have hstable : (prefixWord ++ tailWord_3844439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844439).length < 2 ^ (prefixWord ++ tailWord_3844439).sum := by decide
  have hdescent : baseEnd_3844439 < baseStart_3844439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844450 : List Nat := [3, 3, 2, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_3844450 : Nat := 118140960795 + 3844450 * 2 ^ 59
def prefixEnd_3844450 : Nat := 4983230072969 + 3 ^ 40 * 3844450 * 2
def baseEnd_3844450 : Nat := 1974050702177588805394703

theorem tailTrace_3844450 : CollatzResearch.WordTrace tailWord_3844450 prefixEnd_3844450 1974050702177588805394703 := by
  unfold tailWord_3844450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35054652730555426158030701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93479073948147803088081869 35054652730555426158030701)
  ·
    refine ⟨13145494773958284809261513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35054652730555426158030701 13145494773958284809261513)
    ·
      refine ⟨9859121080468713606946135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13145494773958284809261513 9859121080468713606946135)
      ·
        refine ⟨14788681620703070410419203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859121080468713606946135 14788681620703070410419203)
        ·
          refine ⟨22183022431054605615628805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14788681620703070410419203 22183022431054605615628805)
          ·
            refine ⟨4159316705822738552930401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22183022431054605615628805 4159316705822738552930401)
            ·
              refine ⟨3119487529367053914697801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4159316705822738552930401 3119487529367053914697801)
              ·
                refine ⟨2339615647025290436023351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119487529367053914697801 2339615647025290436023351)
                ·
                  refine ⟨3509423470537935654035027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339615647025290436023351 3509423470537935654035027)
                  ·
                    refine ⟨5264135205806903481052541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3509423470537935654035027 5264135205806903481052541)
                    ·
                      refine ⟨1974050702177588805394703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5264135205806903481052541 1974050702177588805394703)
                      ·
                        rfl

theorem cell23_3844450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_3844450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844450 prefixEnd_3844450 := by exact prefixLift 3844450
  have htrace : WordTrace (prefixWord ++ tailWord_3844450) baseStart_3844450 baseEnd_3844450 := by
    simpa [prefixWord, tailWord_3844450, baseEnd_3844450] using wordTrace_append hprefix tailTrace_3844450
  have hstable : (prefixWord ++ tailWord_3844450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844450).length < 2 ^ (prefixWord ++ tailWord_3844450).sum := by decide
  have hdescent : baseEnd_3844450 < baseStart_3844450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844469 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3844469 : Nat := 118140960795 + 3844469 * 2 ^ 59
def prefixEnd_3844469 : Nat := 4983230072969 + 3 ^ 40 * 3844469 * 2
def baseEnd_3844469 : Nat := 1974060458310024231057115

theorem tailTrace_3844469 : CollatzResearch.WordTrace tailWord_3844469 prefixEnd_3844469 1974060458310024231057115 := by
  unfold tailWord_3844469
  simp only [CollatzResearch.WordTrace]
  refine ⟨140219303909152870877064461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93479535939435247251376307 140219303909152870877064461)
  ·
    refine ⟨52582238965932326578899173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140219303909152870877064461 52582238965932326578899173)
    ·
      refine ⟨9859169806112311233543595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52582238965932326578899173 9859169806112311233543595)
      ·
        refine ⟨14788754709168466850315393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859169806112311233543595 14788754709168466850315393)
        ·
          refine ⟨11091566031876350137736545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14788754709168466850315393 11091566031876350137736545)
          ·
            refine ⟨8318674523907262603302409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11091566031876350137736545 8318674523907262603302409)
            ·
              refine ⟨6239005892930446952476807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318674523907262603302409 6239005892930446952476807)
              ·
                refine ⟨9358508839395670428715211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239005892930446952476807 9358508839395670428715211)
                ·
                  refine ⟨14037763259093505643072817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9358508839395670428715211 14037763259093505643072817)
                  ·
                    refine ⟨10528322444320129232304613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14037763259093505643072817 10528322444320129232304613)
                    ·
                      refine ⟨1974060458310024231057115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10528322444320129232304613 1974060458310024231057115)
                      ·
                        rfl

theorem cell23_3844469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3844469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844469 prefixEnd_3844469 := by exact prefixLift 3844469
  have htrace : WordTrace (prefixWord ++ tailWord_3844469) baseStart_3844469 baseEnd_3844469 := by
    simpa [prefixWord, tailWord_3844469, baseEnd_3844469] using wordTrace_append hprefix tailTrace_3844469
  have hstable : (prefixWord ++ tailWord_3844469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844469).length < 2 ^ (prefixWord ++ tailWord_3844469).sum := by decide
  have hdescent : baseEnd_3844469 < baseStart_3844469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844485 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_3844485 : Nat := 118140960795 + 3844485 * 2 ^ 59
def prefixEnd_3844485 : Nat := 4983230072969 + 3 ^ 40 * 3844485 * 2
def baseEnd_3844485 : Nat := 1974068674000496168457041

theorem tailTrace_3844485 : CollatzResearch.WordTrace tailWord_3844485 prefixEnd_3844485 1974068674000496168457041 := by
  unfold tailWord_3844485
  simp only [CollatzResearch.WordTrace]
  refine ⟨140219887477094905609646909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93479924984729937073097939 140219887477094905609646909)
  ·
    refine ⟨52582457803910589603617591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140219887477094905609646909 52582457803910589603617591)
    ·
      refine ⟨78873686705865884405426387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52582457803910589603617591 78873686705865884405426387)
      ·
        refine ⟨118310530058798826608139581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78873686705865884405426387 118310530058798826608139581)
        ·
          refine ⟨44366448772049559978052343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118310530058798826608139581 44366448772049559978052343)
          ·
            refine ⟨66549673158074339967078515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44366448772049559978052343 66549673158074339967078515)
            ·
              refine ⟨99824509737111509950617773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66549673158074339967078515 99824509737111509950617773)
              ·
                refine ⟨37434191151416816231481665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99824509737111509950617773 37434191151416816231481665)
                ·
                  refine ⟨28075643363562612173611249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37434191151416816231481665 28075643363562612173611249)
                  ·
                    refine ⟨21056732522671959130208437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28075643363562612173611249 21056732522671959130208437)
                    ·
                      refine ⟨1974068674000496168457041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21056732522671959130208437 1974068674000496168457041)
                      ·
                        rfl

theorem cell23_3844485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_3844485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844485 prefixEnd_3844485 := by exact prefixLift 3844485
  have htrace : WordTrace (prefixWord ++ tailWord_3844485) baseStart_3844485 baseEnd_3844485 := by
    simpa [prefixWord, tailWord_3844485, baseEnd_3844485] using wordTrace_append hprefix tailTrace_3844485
  have hstable : (prefixWord ++ tailWord_3844485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844485).length < 2 ^ (prefixWord ++ tailWord_3844485).sum := by decide
  have hdescent : baseEnd_3844485 < baseStart_3844485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844490 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_3844490 : Nat := 118140960795 + 3844490 * 2 ^ 59
def prefixEnd_3844490 : Nat := 4983230072969 + 3 ^ 40 * 3844490 * 2
def baseEnd_3844490 : Nat := 1974071241403768648894519

theorem tailTrace_3844490 : CollatzResearch.WordTrace tailWord_3844490 prefixEnd_3844490 1974071241403768648894519 := by
  unfold tailWord_3844490
  simp only [CollatzResearch.WordTrace]
  refine ⟨35055017460519197865894731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93480046561384527642385949 35055017460519197865894731)
  ·
    refine ⟨52582526190778796798842097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35055017460519197865894731 52582526190778796798842097)
    ·
      refine ⟨39436894643084097599131573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52582526190778796798842097 39436894643084097599131573)
      ·
        refine ⟨3697208872789134149918585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39436894643084097599131573 3697208872789134149918585)
        ·
          refine ⟨2772906654591850612438939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3697208872789134149918585 2772906654591850612438939)
          ·
            refine ⟨4159359981887775918658409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772906654591850612438939 4159359981887775918658409)
            ·
              refine ⟨3119519986415831938993807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4159359981887775918658409 3119519986415831938993807)
              ·
                refine ⟨4679279979623747908490711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119519986415831938993807 4679279979623747908490711)
                ·
                  refine ⟨7018919969435621862736067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679279979623747908490711 7018919969435621862736067)
                  ·
                    refine ⟨10528379954153432794104101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7018919969435621862736067 10528379954153432794104101)
                    ·
                      refine ⟨1974071241403768648894519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10528379954153432794104101 1974071241403768648894519)
                      ·
                        rfl

theorem cell23_3844490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_3844490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844490 prefixEnd_3844490 := by exact prefixLift 3844490
  have htrace : WordTrace (prefixWord ++ tailWord_3844490) baseStart_3844490 baseEnd_3844490 := by
    simpa [prefixWord, tailWord_3844490, baseEnd_3844490] using wordTrace_append hprefix tailTrace_3844490
  have hstable : (prefixWord ++ tailWord_3844490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844490).length < 2 ^ (prefixWord ++ tailWord_3844490).sum := by decide
  have hdescent : baseEnd_3844490 < baseStart_3844490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844505 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 4, 6]
def baseStart_3844505 : Nat := 118140960795 + 3844505 * 2 ^ 59
def prefixEnd_3844505 : Nat := 4983230072969 + 3 ^ 40 * 3844505 * 2
def baseEnd_3844505 : Nat := 658026314537862030068983

theorem tailTrace_3844505 : CollatzResearch.WordTrace tailWord_3844505 prefixEnd_3844505 658026314537862030068983 := by
  unfold tailWord_3844505
  simp only [CollatzResearch.WordTrace]
  refine ⟨140220616937022449025374969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93480411291348299350249979 140220616937022449025374969)
  ·
    refine ⟨105165462702766836769031227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140220616937022449025374969 105165462702766836769031227)
    ·
      refine ⟨157748194054150255153546841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105165462702766836769031227 157748194054150255153546841)
      ·
        refine ⟨118311145540612691365160131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157748194054150255153546841 118311145540612691365160131)
        ·
          refine ⟨177466718310919037047740197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118311145540612691365160131 177466718310919037047740197)
          ·
            refine ⟨33275009683297319446451287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177466718310919037047740197 33275009683297319446451287)
            ·
              refine ⟨49912514524945979169676931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33275009683297319446451287 49912514524945979169676931)
              ·
                refine ⟨74868771787418968754515397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49912514524945979169676931 74868771787418968754515397)
                ·
                  refine ⟨14037894710141056641471637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74868771787418968754515397 14037894710141056641471637)
                  ·
                    refine ⟨658026314537862030068983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14037894710141056641471637 658026314537862030068983)
                    ·
                      rfl

theorem cell23_3844505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_3844505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844505 prefixEnd_3844505 := by exact prefixLift 3844505
  have htrace : WordTrace (prefixWord ++ tailWord_3844505) baseStart_3844505 baseEnd_3844505 := by
    simpa [prefixWord, tailWord_3844505, baseEnd_3844505] using wordTrace_append hprefix tailTrace_3844505
  have hstable : (prefixWord ++ tailWord_3844505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844505).length < 2 ^ (prefixWord ++ tailWord_3844505).sum := by decide
  have hdescent : baseEnd_3844505 < baseStart_3844505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844506 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3844506 : Nat := 118140960795 + 3844506 * 2 ^ 59
def prefixEnd_3844506 : Nat := 4983230072969 + 3 ^ 40 * 3844506 * 2
def baseEnd_3844506 : Nat := 1974079457094240586294445

theorem tailTrace_3844506 : CollatzResearch.WordTrace tailWord_3844506 prefixEnd_3844506 1974079457094240586294445 := by
  unfold tailWord_3844506
  simp only [CollatzResearch.WordTrace]
  refine ⟨35055163352504706549040343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93480435606679217464107581 35055163352504706549040343)
  ·
    refine ⟨52582745028757059823560515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35055163352504706549040343 52582745028757059823560515)
    ·
      refine ⟨78874117543135589735340773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52582745028757059823560515 78874117543135589735340773)
      ·
        refine ⟨14788897039337923075376395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78874117543135589735340773 14788897039337923075376395)
        ·
          refine ⟨22183345559006884613064593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14788897039337923075376395 22183345559006884613064593)
          ·
            refine ⟨16637509169255163459798445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22183345559006884613064593 16637509169255163459798445)
            ·
              refine ⟨6239065938470686297424417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16637509169255163459798445 6239065938470686297424417)
              ·
                refine ⟨4679299453853014723068313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239065938470686297424417 4679299453853014723068313)
                ·
                  refine ⟨3509474590389761042301235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4679299453853014723068313 3509474590389761042301235)
                  ·
                    refine ⟨5264211885584641563451853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3509474590389761042301235 5264211885584641563451853)
                    ·
                      refine ⟨1974079457094240586294445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5264211885584641563451853 1974079457094240586294445)
                      ·
                        rfl

theorem cell23_3844506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3844506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844506 prefixEnd_3844506 := by exact prefixLift 3844506
  have htrace : WordTrace (prefixWord ++ tailWord_3844506) baseStart_3844506 baseEnd_3844506 := by
    simpa [prefixWord, tailWord_3844506, baseEnd_3844506] using wordTrace_append hprefix tailTrace_3844506
  have hstable : (prefixWord ++ tailWord_3844506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844506).length < 2 ^ (prefixWord ++ tailWord_3844506).sum := by decide
  have hdescent : baseEnd_3844506 < baseStart_3844506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844533 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_3844533 : Nat := 118140960795 + 3844533 * 2 ^ 59
def prefixEnd_3844533 : Nat := 4983230072969 + 3 ^ 40 * 3844533 * 2
def baseEnd_3844533 : Nat := 1974093321071911980656821

theorem tailTrace_3844533 : CollatzResearch.WordTrace tailWord_3844533 prefixEnd_3844533 1974093321071911980656821 := by
  unfold tailWord_3844533
  simp only [CollatzResearch.WordTrace]
  refine ⟨140221638180921009807394253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93481092120614006538262835 140221638180921009807394253)
  ·
    refine ⟨52583114317845378677772845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140221638180921009807394253 52583114317845378677772845)
    ·
      refine ⟨19718667869192017004164817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52583114317845378677772845 19718667869192017004164817)
      ·
        refine ⟨14789000901894012753123613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19718667869192017004164817 14789000901894012753123613)
        ·
          refine ⟨5545875338210254782421355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14789000901894012753123613 5545875338210254782421355)
          ·
            refine ⟨8318813007315382173632033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545875338210254782421355 8318813007315382173632033)
            ·
              refine ⟨6239109755486536630224025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318813007315382173632033 6239109755486536630224025)
              ·
                refine ⟨4679332316614902472668019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239109755486536630224025 4679332316614902472668019)
                ·
                  refine ⟨7018998474922353709002029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679332316614902472668019 7018998474922353709002029)
                  ·
                    refine ⟨2632124428095882640875761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7018998474922353709002029 2632124428095882640875761)
                    ·
                      refine ⟨1974093321071911980656821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632124428095882640875761 1974093321071911980656821)
                      ·
                        rfl

theorem cell23_3844533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_3844533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844533 prefixEnd_3844533 := by exact prefixLift 3844533
  have htrace : WordTrace (prefixWord ++ tailWord_3844533) baseStart_3844533 baseEnd_3844533 := by
    simpa [prefixWord, tailWord_3844533, baseEnd_3844533] using wordTrace_append hprefix tailTrace_3844533
  have hstable : (prefixWord ++ tailWord_3844533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844533).length < 2 ^ (prefixWord ++ tailWord_3844533).sum := by decide
  have hdescent : baseEnd_3844533 < baseStart_3844533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844542 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3844542 : Nat := 118140960795 + 3844542 * 2 ^ 59
def prefixEnd_3844542 : Nat := 4983230072969 + 3 ^ 40 * 3844542 * 2
def baseEnd_3844542 : Nat := 1974097942397802445444279

theorem tailTrace_3844542 : CollatzResearch.WordTrace tailWord_3844542 prefixEnd_3844542 1974097942397802445444279 := by
  unfold tailWord_3844542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17527745804736050543058985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93481310958592269562981253 17527745804736050543058985)
  ·
    refine ⟨13145809353552037907294239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17527745804736050543058985 13145809353552037907294239)
    ·
      refine ⟨19718714030328056860941359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13145809353552037907294239 19718714030328056860941359)
      ·
        refine ⟨29578071045492085291412039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19718714030328056860941359 29578071045492085291412039)
        ·
          refine ⟨44367106568238127937118059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29578071045492085291412039 44367106568238127937118059)
          ·
            refine ⟨66550659852357191905677089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44367106568238127937118059 66550659852357191905677089)
            ·
              refine ⟨49912994889267893929257817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66550659852357191905677089 49912994889267893929257817)
              ·
                refine ⟨37434746166950920446943363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49912994889267893929257817 37434746166950920446943363)
                ·
                  refine ⟨56152119250426380670415045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37434746166950920446943363 56152119250426380670415045)
                  ·
                    refine ⟨10528522359454946375702821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56152119250426380670415045 10528522359454946375702821)
                    ·
                      refine ⟨1974097942397802445444279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10528522359454946375702821 1974097942397802445444279)
                      ·
                        rfl

theorem cell23_3844542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3844542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844542 prefixEnd_3844542 := by exact prefixLift 3844542
  have htrace : WordTrace (prefixWord ++ tailWord_3844542) baseStart_3844542 baseEnd_3844542 := by
    simpa [prefixWord, tailWord_3844542, baseEnd_3844542] using wordTrace_append hprefix tailTrace_3844542
  have hstable : (prefixWord ++ tailWord_3844542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844542).length < 2 ^ (prefixWord ++ tailWord_3844542).sum := by decide
  have hdescent : baseEnd_3844542 < baseStart_3844542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844614 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3844614 : Nat := 118140960795 + 3844614 * 2 ^ 59
def prefixEnd_3844614 : Nat := 4983230072969 + 3 ^ 40 * 3844614 * 2
def baseEnd_3844614 : Nat := 1974134913004926163743949

theorem tailTrace_3844614 : CollatzResearch.WordTrace tailWord_3844614 prefixEnd_3844614 1974134913004926163743949 := by
  unfold tailWord_3844614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4382018515425861270034153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93483061662418373760728597 4382018515425861270034153)
  ·
    refine ⟨3286513886569395952525615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4382018515425861270034153 3286513886569395952525615)
    ·
      refine ⟨4929770829854093928788423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286513886569395952525615 4929770829854093928788423)
      ·
        refine ⟨7394656244781140893182635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4929770829854093928788423 7394656244781140893182635)
        ·
          refine ⟨11091984367171711339773953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7394656244781140893182635 11091984367171711339773953)
          ·
            refine ⟨8318988275378783504830465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11091984367171711339773953 8318988275378783504830465)
            ·
              refine ⟨6239241206534087628622849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318988275378783504830465 6239241206534087628622849)
              ·
                refine ⟨4679430904900565721467137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239241206534087628622849 4679430904900565721467137)
                ·
                  refine ⟨3509573178675424291100353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4679430904900565721467137 3509573178675424291100353)
                  ·
                    refine ⟨2632179884006568218325265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3509573178675424291100353 2632179884006568218325265)
                    ·
                      refine ⟨1974134913004926163743949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632179884006568218325265 1974134913004926163743949)
                      ·
                        rfl

theorem cell23_3844614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3844614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844614 prefixEnd_3844614 := by exact prefixLift 3844614
  have htrace : WordTrace (prefixWord ++ tailWord_3844614) baseStart_3844614 baseEnd_3844614 := by
    simpa [prefixWord, tailWord_3844614, baseEnd_3844614] using wordTrace_append hprefix tailTrace_3844614
  have hstable : (prefixWord ++ tailWord_3844614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844614).length < 2 ^ (prefixWord ++ tailWord_3844614).sum := by decide
  have hdescent : baseEnd_3844614 < baseStart_3844614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844619 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 4]
def baseStart_3844619 : Nat := 118140960795 + 3844619 * 2 ^ 59
def prefixEnd_3844619 : Nat := 4983230072969 + 3 ^ 40 * 3844619 * 2
def baseEnd_3844619 : Nat := 1974137480408198644181425

theorem tailTrace_3844619 : CollatzResearch.WordTrace tailWord_3844619 prefixEnd_3844619 1974137480408198644181425 := by
  unfold tailWord_3844619
  simp only [CollatzResearch.WordTrace]
  refine ⟨140224774858609446495024911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93483183239072964330016607 140224774858609446495024911)
  ·
    refine ⟨210337162287914169742537367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140224774858609446495024911 210337162287914169742537367)
    ·
      refine ⟨315505743431871254613806051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210337162287914169742537367 315505743431871254613806051)
      ·
        refine ⟨473258615147806881920709077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315505743431871254613806051 473258615147806881920709077)
        ·
          refine ⟨11091998792526723795016619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 473258615147806881920709077 11091998792526723795016619)
          ·
            refine ⟨16637998188790085692524929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11091998792526723795016619 16637998188790085692524929)
            ·
              refine ⟨12478498641592564269393697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16637998188790085692524929 12478498641592564269393697)
              ·
                refine ⟨9358873981194423202045273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12478498641592564269393697 9358873981194423202045273)
                ·
                  refine ⟨7019155485895817401533955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9358873981194423202045273 7019155485895817401533955)
                  ·
                    refine ⟨10528733228843726102300933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7019155485895817401533955 10528733228843726102300933)
                    ·
                      refine ⟨1974137480408198644181425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10528733228843726102300933 1974137480408198644181425)
                      ·
                        rfl

theorem cell23_3844619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 4].length) (baseStart_3844619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844619 prefixEnd_3844619 := by exact prefixLift 3844619
  have htrace : WordTrace (prefixWord ++ tailWord_3844619) baseStart_3844619 baseEnd_3844619 := by
    simpa [prefixWord, tailWord_3844619, baseEnd_3844619] using wordTrace_append hprefix tailTrace_3844619
  have hstable : (prefixWord ++ tailWord_3844619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844619).length < 2 ^ (prefixWord ++ tailWord_3844619).sum := by decide
  have hdescent : baseEnd_3844619 < baseStart_3844619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844629 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_3844629 : Nat := 118140960795 + 3844629 * 2 ^ 59
def prefixEnd_3844629 : Nat := 4983230072969 + 3 ^ 40 * 3844629 * 2
def baseEnd_3844629 : Nat := 658047538404914535018793

theorem tailTrace_3844629 : CollatzResearch.WordTrace tailWord_3844629 prefixEnd_3844629 658047538404914535018793 := by
  unfold tailWord_3844629
  simp only [CollatzResearch.WordTrace]
  refine ⟨140225139588573218202888941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93483426392382145468592627 140225139588573218202888941)
  ·
    refine ⟨52584427345714956826083353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140225139588573218202888941 52584427345714956826083353)
    ·
      refine ⟨39438320509286217619562515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52584427345714956826083353 39438320509286217619562515)
      ·
        refine ⟨59157480763929326429343773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39438320509286217619562515 59157480763929326429343773)
        ·
          refine ⟨22184055286473497411003915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59157480763929326429343773 22184055286473497411003915)
          ·
            refine ⟨33276082929710246116505873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22184055286473497411003915 33276082929710246116505873)
            ·
              refine ⟨24957062197282684587379405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33276082929710246116505873 24957062197282684587379405)
              ·
                refine ⟨9358898323981006720267277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24957062197282684587379405 9358898323981006720267277)
                ·
                  refine ⟨3509586871492877520100229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9358898323981006720267277 3509586871492877520100229)
                  ·
                    refine ⟨658047538404914535018793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3509586871492877520100229 658047538404914535018793)
                    ·
                      rfl

theorem cell23_3844629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_3844629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844629 prefixEnd_3844629 := by exact prefixLift 3844629
  have htrace : WordTrace (prefixWord ++ tailWord_3844629) baseStart_3844629 baseEnd_3844629 := by
    simpa [prefixWord, tailWord_3844629, baseEnd_3844629] using wordTrace_append hprefix tailTrace_3844629
  have hstable : (prefixWord ++ tailWord_3844629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844629).length < 2 ^ (prefixWord ++ tailWord_3844629).sum := by decide
  have hdescent : baseEnd_3844629 < baseStart_3844629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844636 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_3844636 : Nat := 118140960795 + 3844636 * 2 ^ 59
def prefixEnd_3844636 : Nat := 4983230072969 + 3 ^ 40 * 3844636 * 2
def baseEnd_3844636 : Nat := 1974146209579325077668847

theorem tailTrace_3844636 : CollatzResearch.WordTrace tailWord_3844636 prefixEnd_3844636 1974146209579325077668847 := by
  unfold tailWord_3844636
  simp only [CollatzResearch.WordTrace]
  refine ⟨70112697449773929199196881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93483596599698572265595841 70112697449773929199196881)
  ·
    refine ⟨52584523087330446899397661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70112697449773929199196881 52584523087330446899397661)
    ·
      refine ⟨19719196157748917587274123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52584523087330446899397661 19719196157748917587274123)
      ·
        refine ⟨29578794236623376380911185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19719196157748917587274123 29578794236623376380911185)
        ·
          refine ⟨22184095677467532285683389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29578794236623376380911185 22184095677467532285683389)
          ·
            refine ⟨8319035879050324607131271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22184095677467532285683389 8319035879050324607131271)
            ·
              refine ⟨12478553818575486910696907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319035879050324607131271 12478553818575486910696907)
              ·
                refine ⟨18717830727863230366045361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12478553818575486910696907 18717830727863230366045361)
                ·
                  refine ⟨14038373045897422774534021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18717830727863230366045361 14038373045897422774534021)
                  ·
                    refine ⟨2632194946105766770225129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14038373045897422774534021 2632194946105766770225129)
                    ·
                      refine ⟨1974146209579325077668847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632194946105766770225129 1974146209579325077668847)
                      ·
                        rfl

theorem cell23_3844636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_3844636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844636 prefixEnd_3844636 := by exact prefixLift 3844636
  have htrace : WordTrace (prefixWord ++ tailWord_3844636) baseStart_3844636 baseEnd_3844636 := by
    simpa [prefixWord, tailWord_3844636, baseEnd_3844636] using wordTrace_append hprefix tailTrace_3844636
  have hstable : (prefixWord ++ tailWord_3844636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844636).length < 2 ^ (prefixWord ++ tailWord_3844636).sum := by decide
  have hdescent : baseEnd_3844636 < baseStart_3844636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844642 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 10]
def baseStart_3844642 : Nat := 118140960795 + 3844642 * 2 ^ 59
def prefixEnd_3844642 : Nat := 4983230072969 + 3 ^ 40 * 3844642 * 2
def baseEnd_3844642 : Nat := 219349921162583561577091

theorem tailTrace_3844642 : CollatzResearch.WordTrace tailWord_3844642 prefixEnd_3844642 219349921162583561577091 := by
  unfold tailWord_3844642
  simp only [CollatzResearch.WordTrace]
  refine ⟨35056403434381530355778045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93483742491684080948741453 35056403434381530355778045)
  ·
    refine ⟨13146151287893073883416767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35056403434381530355778045 13146151287893073883416767)
    ·
      refine ⟨19719226931839610825125151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13146151287893073883416767 19719226931839610825125151)
      ·
        refine ⟨29578840397759416237687727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19719226931839610825125151 29578840397759416237687727)
        ·
          refine ⟨44368260596639124356531591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29578840397759416237687727 44368260596639124356531591)
          ·
            refine ⟨66552390894958686534797387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44368260596639124356531591 66552390894958686534797387)
            ·
              refine ⟨99828586342438029802196081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66552390894958686534797387 99828586342438029802196081)
              ·
                refine ⟨74871439756828522351647061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99828586342438029802196081 74871439756828522351647061)
                ·
                  refine ⟨219349921162583561577091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 74871439756828522351647061 219349921162583561577091)
                  ·
                    rfl

theorem cell23_3844642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_3844642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844642 prefixEnd_3844642 := by exact prefixLift 3844642
  have htrace : WordTrace (prefixWord ++ tailWord_3844642) baseStart_3844642 baseEnd_3844642 := by
    simpa [prefixWord, tailWord_3844642, baseEnd_3844642] using wordTrace_append hprefix tailTrace_3844642
  have hstable : (prefixWord ++ tailWord_3844642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844642).length < 2 ^ (prefixWord ++ tailWord_3844642).sum := by decide
  have hdescent : baseEnd_3844642 < baseStart_3844642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844686 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_3844686 : Nat := 118140960795 + 3844686 * 2 ^ 59
def prefixEnd_3844686 : Nat := 4983230072969 + 3 ^ 40 * 3844686 * 2
def baseEnd_3844686 : Nat := 1974171883612049882043617

theorem tailTrace_3844686 : CollatzResearch.WordTrace tailWord_3844686 prefixEnd_3844686 1974171883612049882043617 := by
  unfold tailWord_3844686
  simp only [CollatzResearch.WordTrace]
  refine ⟨17528402318670839617214239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93484812366244477958475941 17528402318670839617214239)
  ·
    refine ⟨26292603478006259425821359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17528402318670839617214239 26292603478006259425821359)
    ·
      refine ⟨39438905217009389138732039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26292603478006259425821359 39438905217009389138732039)
      ·
        refine ⟨59158357825514083708098059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39438905217009389138732039 59158357825514083708098059)
        ·
          refine ⟨88737536738271125562147089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59158357825514083708098059 88737536738271125562147089)
          ·
            refine ⟨66553152553703344171610317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88737536738271125562147089 66553152553703344171610317)
            ·
              refine ⟨24957432207638754064353869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66553152553703344171610317 24957432207638754064353869)
              ·
                refine ⟨9359037077864532774132701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24957432207638754064353869 9359037077864532774132701)
                ·
                  refine ⟨3509638904199199790299763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9359037077864532774132701 3509638904199199790299763)
                  ·
                    refine ⟨5264458356298799685449645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3509638904199199790299763 5264458356298799685449645)
                    ·
                      refine ⟨1974171883612049882043617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5264458356298799685449645 1974171883612049882043617)
                      ·
                        rfl

theorem cell23_3844686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_3844686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844686 prefixEnd_3844686 := by exact prefixLift 3844686
  have htrace : WordTrace (prefixWord ++ tailWord_3844686) baseStart_3844686 baseEnd_3844686 := by
    simpa [prefixWord, tailWord_3844686, baseEnd_3844686] using wordTrace_append hprefix tailTrace_3844686
  have hstable : (prefixWord ++ tailWord_3844686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844686).length < 2 ^ (prefixWord ++ tailWord_3844686).sum := by decide
  have hdescent : baseEnd_3844686 < baseStart_3844686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844719 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 4, 4]
def baseStart_3844719 : Nat := 118140960795 + 3844719 * 2 ^ 59
def prefixEnd_3844719 : Nat := 4983230072969 + 3 ^ 40 * 3844719 * 2
def baseEnd_3844719 : Nat := 658062942824549417643655

theorem tailTrace_3844719 : CollatzResearch.WordTrace tailWord_3844719 prefixEnd_3844719 658062942824549417643655 := by
  unfold tailWord_3844719
  simp only [CollatzResearch.WordTrace]
  refine ⟨140228422158247163573665211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93485614772164775715776807 140228422158247163573665211)
  ·
    refine ⟨210342633237370745360497817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140228422158247163573665211 210342633237370745360497817)
    ·
      refine ⟨157756974928028059020373363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210342633237370745360497817 157756974928028059020373363)
      ·
        refine ⟨236635462392042088530560045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157756974928028059020373363 236635462392042088530560045)
        ·
          refine ⟨88738298397015783198960017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236635462392042088530560045 88738298397015783198960017)
          ·
            refine ⟨66553723797761837399220013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88738298397015783198960017 66553723797761837399220013)
            ·
              refine ⟨24957646424160689024707505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66553723797761837399220013 24957646424160689024707505)
              ·
                refine ⟨18718234818120516768530629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24957646424160689024707505 18718234818120516768530629)
                ·
                  refine ⟨3509669028397596894099493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18718234818120516768530629 3509669028397596894099493)
                  ·
                    refine ⟨658062942824549417643655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3509669028397596894099493 658062942824549417643655)
                    ·
                      rfl

theorem cell23_3844719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 4].length) (baseStart_3844719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844719 prefixEnd_3844719 := by exact prefixLift 3844719
  have htrace : WordTrace (prefixWord ++ tailWord_3844719) baseStart_3844719 baseEnd_3844719 := by
    simpa [prefixWord, tailWord_3844719, baseEnd_3844719] using wordTrace_append hprefix tailTrace_3844719
  have hstable : (prefixWord ++ tailWord_3844719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844719).length < 2 ^ (prefixWord ++ tailWord_3844719).sum := by decide
  have hdescent : baseEnd_3844719 < baseStart_3844719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844729 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_3844729 : Nat := 118140960795 + 3844729 * 2 ^ 59
def prefixEnd_3844729 : Nat := 4983230072969 + 3 ^ 40 * 3844729 * 2
def baseEnd_3844729 : Nat := 1974193963280193213805919

theorem tailTrace_3844729 : CollatzResearch.WordTrace tailWord_3844729 prefixEnd_3844729 1974193963280193213805919 := by
  unfold tailWord_3844729
  simp only [CollatzResearch.WordTrace]
  refine ⟨140228786888210935281529241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93485857925473956854352827 140228786888210935281529241)
  ·
    refine ⟨105171590166158201461146931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140228786888210935281529241 105171590166158201461146931)
    ·
      refine ⟨157757385249237302191720397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105171590166158201461146931 157757385249237302191720397)
      ·
        refine ⟨59159019468463988321895149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157757385249237302191720397 59159019468463988321895149)
        ·
          refine ⟨22184632300673995620710681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59159019468463988321895149 22184632300673995620710681)
          ·
            refine ⟨16638474225505496715533011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22184632300673995620710681 16638474225505496715533011)
            ·
              refine ⟨24957711338258245073299517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16638474225505496715533011 24957711338258245073299517)
              ·
                refine ⟨9359141751846841902487319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24957711338258245073299517 9359141751846841902487319)
                ·
                  refine ⟨14038712627770262853730979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359141751846841902487319 14038712627770262853730979)
                  ·
                    refine ⟨21058068941655394280596469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14038712627770262853730979 21058068941655394280596469)
                    ·
                      refine ⟨1974193963280193213805919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21058068941655394280596469 1974193963280193213805919)
                      ·
                        rfl

theorem cell23_3844729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_3844729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844729 prefixEnd_3844729 := by exact prefixLift 3844729
  have htrace : WordTrace (prefixWord ++ tailWord_3844729) baseStart_3844729 baseEnd_3844729 := by
    simpa [prefixWord, tailWord_3844729, baseEnd_3844729] using wordTrace_append hprefix tailTrace_3844729
  have hstable : (prefixWord ++ tailWord_3844729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844729).length < 2 ^ (prefixWord ++ tailWord_3844729).sum := by decide
  have hdescent : baseEnd_3844729 < baseStart_3844729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844732 : List Nat := [2, 2, 2, 1, 1, 2, 13]
def baseStart_3844732 : Nat := 118140960795 + 3844732 * 2 ^ 59
def prefixEnd_3844732 : Nat := 4983230072969 + 3 ^ 40 * 3844732 * 2
def baseEnd_3844732 : Nat := 24372783996569835828005

theorem tailTrace_3844732 : CollatzResearch.WordTrace tailWord_3844732 prefixEnd_3844732 24372783996569835828005 := by
  unfold tailWord_3844732
  simp only [CollatzResearch.WordTrace]
  refine ⟨70114448153600033396944225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93485930871466711195925633 70114448153600033396944225)
  ·
    refine ⟨52585836115200025047708169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70114448153600033396944225 52585836115200025047708169)
    ·
      refine ⟨39439377086400018785781127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52585836115200025047708169 39439377086400018785781127)
      ·
        refine ⟨59159065629600028178671691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39439377086400018785781127 59159065629600028178671691)
        ·
          refine ⟨88738598444400042268007537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59159065629600028178671691 88738598444400042268007537)
          ·
            refine ⟨66553948833300031701005653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88738598444400042268007537 66553948833300031701005653)
            ·
              refine ⟨24372783996569835828005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 66553948833300031701005653 24372783996569835828005)
              ·
                rfl

theorem cell23_3844732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 13].length) (baseStart_3844732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844732 prefixEnd_3844732 := by exact prefixLift 3844732
  have htrace : WordTrace (prefixWord ++ tailWord_3844732) baseStart_3844732 baseEnd_3844732 := by
    simpa [prefixWord, tailWord_3844732, baseEnd_3844732] using wordTrace_append hprefix tailTrace_3844732
  have hstable : (prefixWord ++ tailWord_3844732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844732).length < 2 ^ (prefixWord ++ tailWord_3844732).sum := by decide
  have hdescent : baseEnd_3844732 < baseStart_3844732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844756 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3844756 : Nat := 118140960795 + 3844756 * 2 ^ 59
def prefixEnd_3844756 : Nat := 4983230072969 + 3 ^ 40 * 3844756 * 2
def baseEnd_3844756 : Nat := 1974207827257864608168295

theorem tailTrace_3844756 : CollatzResearch.WordTrace tailWord_3844756 prefixEnd_3844756 1974207827257864608168295 := by
  unfold tailWord_3844756
  simp only [CollatzResearch.WordTrace]
  refine ⟨70114885829556559446381061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93486514439408745928508081 70114885829556559446381061)
  ·
    refine ⟨13146541093041854896196449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70114885829556559446381061 13146541093041854896196449)
    ·
      refine ⟨9859905819781391172147337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13146541093041854896196449 9859905819781391172147337)
      ·
        refine ⟨7394929364836043379110503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9859905819781391172147337 7394929364836043379110503)
        ·
          refine ⟨11092394047254065068665755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7394929364836043379110503 11092394047254065068665755)
          ·
            refine ⟨16638591070881097602998633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092394047254065068665755 16638591070881097602998633)
            ·
              refine ⟨12478943303160823202248975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16638591070881097602998633 12478943303160823202248975)
              ·
                refine ⟨18718414954741234803373463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12478943303160823202248975 18718414954741234803373463)
                ·
                  refine ⟨28077622432111852205060195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18718414954741234803373463 28077622432111852205060195)
                  ·
                    refine ⟨42116433648167778307590293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28077622432111852205060195 42116433648167778307590293)
                    ·
                      refine ⟨1974207827257864608168295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42116433648167778307590293 1974207827257864608168295)
                      ·
                        rfl

theorem cell23_3844756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3844756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844756 prefixEnd_3844756 := by exact prefixLift 3844756
  have htrace : WordTrace (prefixWord ++ tailWord_3844756) baseStart_3844756 baseEnd_3844756 := by
    simpa [prefixWord, tailWord_3844756, baseEnd_3844756] using wordTrace_append hprefix tailTrace_3844756
  have hstable : (prefixWord ++ tailWord_3844756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844756).length < 2 ^ (prefixWord ++ tailWord_3844756).sum := by decide
  have hdescent : baseEnd_3844756 < baseStart_3844756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844799 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_3844799 : Nat := 118140960795 + 3844799 * 2 ^ 59
def prefixEnd_3844799 : Nat := 4983230072969 + 3 ^ 40 * 3844799 * 2
def baseEnd_3844799 : Nat := 1974229906926007939930597

theorem tailTrace_3844799 : CollatzResearch.WordTrace tailWord_3844799 prefixEnd_3844799 1974229906926007939930597 := by
  unfold tailWord_3844799
  simp only [CollatzResearch.WordTrace]
  refine ⟨140231339997957337236577451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93487559998638224824384967 140231339997957337236577451)
  ·
    refine ⟨210347009996936005854866177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140231339997957337236577451 210347009996936005854866177)
    ·
      refine ⟨157760257497702004391149633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210347009996936005854866177 157760257497702004391149633)
      ·
        refine ⟨118320193123276503293362225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157760257497702004391149633 118320193123276503293362225)
        ·
          refine ⟨88740144842457377470021669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118320193123276503293362225 88740144842457377470021669)
          ·
            refine ⟨16638777157960758275629063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88740144842457377470021669 16638777157960758275629063)
            ·
              refine ⟨24958165736941137413443595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16638777157960758275629063 24958165736941137413443595)
              ·
                refine ⟨37437248605411706120165393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24958165736941137413443595 37437248605411706120165393)
                ·
                  refine ⟨28077936454058779590124045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37437248605411706120165393 28077936454058779590124045)
                  ·
                    refine ⟨10529226170272042346296517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28077936454058779590124045 10529226170272042346296517)
                    ·
                      refine ⟨1974229906926007939930597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10529226170272042346296517 1974229906926007939930597)
                      ·
                        rfl

theorem cell23_3844799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_3844799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844799 prefixEnd_3844799 := by exact prefixLift 3844799
  have htrace : WordTrace (prefixWord ++ tailWord_3844799) baseStart_3844799 baseEnd_3844799 := by
    simpa [prefixWord, tailWord_3844799, baseEnd_3844799] using wordTrace_append hprefix tailTrace_3844799
  have hstable : (prefixWord ++ tailWord_3844799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844799).length < 2 ^ (prefixWord ++ tailWord_3844799).sum := by decide
  have hdescent : baseEnd_3844799 < baseStart_3844799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844833 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_3844833 : Nat := 118140960795 + 3844833 * 2 ^ 59
def prefixEnd_3844833 : Nat := 4983230072969 + 3 ^ 40 * 3844833 * 2
def baseEnd_3844833 : Nat := 1974247365268260806905441

theorem tailTrace_3844833 : CollatzResearch.WordTrace tailWord_3844833 prefixEnd_3844833 1974247365268260806905441 := by
  unfold tailWord_3844833
  simp only [CollatzResearch.WordTrace]
  refine ⟨140232580079834161043315153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93488386719889440695543435 140232580079834161043315153)
  ·
    refine ⟨105174435059875620782486365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140232580079834161043315153 105174435059875620782486365)
    ·
      refine ⟨39440413147453357793432387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105174435059875620782486365 39440413147453357793432387)
      ·
        refine ⟨59160619721180036690148581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39440413147453357793432387 59160619721180036690148581)
        ·
          refine ⟨11092616197721256879402859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59160619721180036690148581 11092616197721256879402859)
          ·
            refine ⟨16638924296581885319104289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092616197721256879402859 16638924296581885319104289)
            ·
              refine ⟨12479193222436413989328217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16638924296581885319104289 12479193222436413989328217)
              ·
                refine ⟨9359394916827310491996163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12479193222436413989328217 9359394916827310491996163)
                ·
                  refine ⟨14039092375240965737994245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359394916827310491996163 14039092375240965737994245)
                  ·
                    refine ⟨2632329820357681075873921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14039092375240965737994245 2632329820357681075873921)
                    ·
                      refine ⟨1974247365268260806905441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632329820357681075873921 1974247365268260806905441)
                      ·
                        rfl

theorem cell23_3844833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_3844833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844833 prefixEnd_3844833 := by exact prefixLift 3844833
  have htrace : WordTrace (prefixWord ++ tailWord_3844833) baseStart_3844833 baseEnd_3844833 := by
    simpa [prefixWord, tailWord_3844833, baseEnd_3844833] using wordTrace_append hprefix tailTrace_3844833
  have hstable : (prefixWord ++ tailWord_3844833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844833).length < 2 ^ (prefixWord ++ tailWord_3844833).sum := by decide
  have hdescent : baseEnd_3844833 < baseStart_3844833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844837 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 1, 3, 2]
def baseStart_3844837 : Nat := 118140960795 + 3844837 * 2 ^ 59
def prefixEnd_3844837 : Nat := 4983230072969 + 3 ^ 40 * 3844837 * 2
def baseEnd_3844837 : Nat := 1974249419190878791255423

theorem tailTrace_3844837 : CollatzResearch.WordTrace tailWord_3844837 prefixEnd_3844837 1974249419190878791255423 := by
  unfold tailWord_3844837
  simp only [CollatzResearch.WordTrace]
  refine ⟨140232725971819669726460765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93488483981213113150973843 140232725971819669726460765)
  ·
    refine ⟨52587272239432376147422787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140232725971819669726460765 52587272239432376147422787)
    ·
      refine ⟨78880908359148564221134181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52587272239432376147422787 78880908359148564221134181)
      ·
        refine ⟨14790170317340355791462659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78880908359148564221134181 14790170317340355791462659)
        ·
          refine ⟨22185255476010533687193989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14790170317340355791462659 22185255476010533687193989)
          ·
            refine ⟨4159735401751975066348873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22185255476010533687193989 4159735401751975066348873)
            ·
              refine ⟨3119801551313981299761655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4159735401751975066348873 3119801551313981299761655)
              ·
                refine ⟨4679702326970971949642483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119801551313981299761655 4679702326970971949642483)
                ·
                  refine ⟨7019553490456457924463725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679702326970971949642483 7019553490456457924463725)
                  ·
                    refine ⟨2632332558921171721673897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7019553490456457924463725 2632332558921171721673897)
                    ·
                      refine ⟨1974249419190878791255423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632332558921171721673897 1974249419190878791255423)
                      ·
                        rfl

theorem cell23_3844837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_3844837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844837 prefixEnd_3844837 := by exact prefixLift 3844837
  have htrace : WordTrace (prefixWord ++ tailWord_3844837) baseStart_3844837 baseEnd_3844837 := by
    simpa [prefixWord, tailWord_3844837, baseEnd_3844837] using wordTrace_append hprefix tailTrace_3844837
  have hstable : (prefixWord ++ tailWord_3844837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844837).length < 2 ^ (prefixWord ++ tailWord_3844837).sum := by decide
  have hdescent : baseEnd_3844837 < baseStart_3844837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844846 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3844846 : Nat := 118140960795 + 3844846 * 2 ^ 59
def prefixEnd_3844846 : Nat := 4983230072969 + 3 ^ 40 * 3844846 * 2
def baseEnd_3844846 : Nat := 1974254040516769256042881

theorem tailTrace_3844846 : CollatzResearch.WordTrace tailWord_3844846 prefixEnd_3844846 1974254040516769256042881 := by
  unfold tailWord_3844846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17529131778598383032942299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93488702819191376175692261 17529131778598383032942299)
  ·
    refine ⟨26293697667897574549413449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17529131778598383032942299 26293697667897574549413449)
    ·
      refine ⟨19720273250923180912060087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26293697667897574549413449 19720273250923180912060087)
      ·
        refine ⟨29580409876384771368090131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19720273250923180912060087 29580409876384771368090131)
        ·
          refine ⟨44370614814577157052135197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29580409876384771368090131 44370614814577157052135197)
          ·
            refine ⟨16638980555466433894550699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44370614814577157052135197 16638980555466433894550699)
            ·
              refine ⟨24958470833199650841826049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16638980555466433894550699 24958470833199650841826049)
              ·
                refine ⟨18718853124899738131369537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24958470833199650841826049 18718853124899738131369537)
                ·
                  refine ⟨14039139843674803598527153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18718853124899738131369537 14039139843674803598527153)
                  ·
                    refine ⟨10529354882756102698895365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14039139843674803598527153 10529354882756102698895365)
                    ·
                      refine ⟨1974254040516769256042881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10529354882756102698895365 1974254040516769256042881)
                      ·
                        rfl

theorem cell23_3844846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3844846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844846 prefixEnd_3844846 := by exact prefixLift 3844846
  have htrace : WordTrace (prefixWord ++ tailWord_3844846) baseStart_3844846 baseEnd_3844846 := by
    simpa [prefixWord, tailWord_3844846, baseEnd_3844846] using wordTrace_append hprefix tailTrace_3844846
  have hstable : (prefixWord ++ tailWord_3844846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844846).length < 2 ^ (prefixWord ++ tailWord_3844846).sum := by decide
  have hdescent : baseEnd_3844846 < baseStart_3844846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844850 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_3844850 : Nat := 118140960795 + 3844850 * 2 ^ 59
def prefixEnd_3844850 : Nat := 4983230072969 + 3 ^ 40 * 3844850 * 2
def baseEnd_3844850 : Nat := 1974256094439387240392863

theorem tailTrace_3844850 : CollatzResearch.WordTrace tailWord_3844850 prefixEnd_3844850 1974256094439387240392863 := by
  unfold tailWord_3844850
  simp only [CollatzResearch.WordTrace]
  refine ⟨35058300030193143236671001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93488800080515048631122669 35058300030193143236671001)
  ·
    refine ⟨26293725022644857427503251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35058300030193143236671001 26293725022644857427503251)
    ·
      refine ⟨39440587533967286141254877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26293725022644857427503251 39440587533967286141254877)
      ·
        refine ⟨14790220325237732302970579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39440587533967286141254877 14790220325237732302970579)
        ·
          refine ⟨22185330487856598454455869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14790220325237732302970579 22185330487856598454455869)
          ·
            refine ⟨8319498932946224420420951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22185330487856598454455869 8319498932946224420420951)
            ·
              refine ⟨12479248399419336630631427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319498932946224420420951 12479248399419336630631427)
              ·
                refine ⟨18718872599129004945947141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12479248399419336630631427 18718872599129004945947141)
                ·
                  refine ⟨3509788612336688427365089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18718872599129004945947141 3509788612336688427365089)
                  ·
                    refine ⟨2632341459252516320523817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3509788612336688427365089 2632341459252516320523817)
                    ·
                      refine ⟨1974256094439387240392863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632341459252516320523817 1974256094439387240392863)
                      ·
                        rfl

theorem cell23_3844850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_3844850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844850 prefixEnd_3844850 := by exact prefixLift 3844850
  have htrace : WordTrace (prefixWord ++ tailWord_3844850) baseStart_3844850 baseEnd_3844850 := by
    simpa [prefixWord, tailWord_3844850, baseEnd_3844850] using wordTrace_append hprefix tailTrace_3844850
  have hstable : (prefixWord ++ tailWord_3844850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844850).length < 2 ^ (prefixWord ++ tailWord_3844850).sum := by decide
  have hdescent : baseEnd_3844850 < baseStart_3844850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844856 : List Nat := [2, 1, 2, 1, 1, 2, 3, 6, 5]
def baseStart_3844856 : Nat := 118140960795 + 3844856 * 2 ^ 59
def prefixEnd_3844856 : Nat := 4983230072969 + 3 ^ 40 * 3844856 * 2
def baseEnd_3844856 : Nat := 219362130591479357435315

theorem tailTrace_3844856 : CollatzResearch.WordTrace tailWord_3844856 prefixEnd_3844856 219362130591479357435315 := by
  unfold tailWord_3844856
  simp only [CollatzResearch.WordTrace]
  refine ⟨70116709479375417985701211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93488945972500557314268281 70116709479375417985701211)
  ·
    refine ⟨105175064219063126978551817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70116709479375417985701211 105175064219063126978551817)
    ·
      refine ⟨78881298164297345233913863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105175064219063126978551817 78881298164297345233913863)
      ·
        refine ⟨118321947246446017850870795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78881298164297345233913863 118321947246446017850870795)
        ·
          refine ⟨177482920869669026776306193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118321947246446017850870795 177482920869669026776306193)
          ·
            refine ⟨133112190652251770082229645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177482920869669026776306193 133112190652251770082229645)
            ·
              refine ⟨49917071494594413780836117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133112190652251770082229645 49917071494594413780836117)
              ·
                refine ⟨2339862726309113145976693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49917071494594413780836117 2339862726309113145976693)
                ·
                  refine ⟨219362130591479357435315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2339862726309113145976693 219362130591479357435315)
                  ·
                    rfl

theorem cell23_3844856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 5].length) (baseStart_3844856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844856 prefixEnd_3844856 := by exact prefixLift 3844856
  have htrace : WordTrace (prefixWord ++ tailWord_3844856) baseStart_3844856 baseEnd_3844856 := by
    simpa [prefixWord, tailWord_3844856, baseEnd_3844856] using wordTrace_append hprefix tailTrace_3844856
  have hstable : (prefixWord ++ tailWord_3844856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844856).length < 2 ^ (prefixWord ++ tailWord_3844856).sum := by decide
  have hdescent : baseEnd_3844856 < baseStart_3844856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844918 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3844918 : Nat := 118140960795 + 3844918 * 2 ^ 59
def prefixEnd_3844918 : Nat := 4983230072969 + 3 ^ 40 * 3844918 * 2
def baseEnd_3844918 : Nat := 1974291011123892974342551

theorem tailTrace_3844918 : CollatzResearch.WordTrace tailWord_3844918 prefixEnd_3844918 1974291011123892974342551 := by
  unfold tailWord_3844918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8764730017782888785009963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93490453523017480373439605 8764730017782888785009963)
  ·
    refine ⟨13147095026674333177514945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8764730017782888785009963 13147095026674333177514945)
    ·
      refine ⟨9860321270005749883136209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13147095026674333177514945 9860321270005749883136209)
      ·
        refine ⟨7395240952504312412352157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9860321270005749883136209 7395240952504312412352157)
        ·
          refine ⟨2773215357189117154632059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7395240952504312412352157 2773215357189117154632059)
          ·
            refine ⟨4159823035783675731948089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773215357189117154632059 4159823035783675731948089)
            ·
              refine ⟨3119867276837756798961067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4159823035783675731948089 3119867276837756798961067)
              ·
                refine ⟨4679800915256635198441601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119867276837756798961067 4679800915256635198441601)
                ·
                  refine ⟨3509850686442476398831201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4679800915256635198441601 3509850686442476398831201)
                  ·
                    refine ⟨2632388014831857299123401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3509850686442476398831201 2632388014831857299123401)
                    ·
                      refine ⟨1974291011123892974342551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632388014831857299123401 1974291011123892974342551)
                      ·
                        rfl

theorem cell23_3844918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3844918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844918 prefixEnd_3844918 := by exact prefixLift 3844918
  have htrace : WordTrace (prefixWord ++ tailWord_3844918) baseStart_3844918 baseEnd_3844918 := by
    simpa [prefixWord, tailWord_3844918, baseEnd_3844918] using wordTrace_append hprefix tailTrace_3844918
  have hstable : (prefixWord ++ tailWord_3844918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844918).length < 2 ^ (prefixWord ++ tailWord_3844918).sum := by decide
  have hdescent : baseEnd_3844918 < baseStart_3844918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844963 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 6]
def baseStart_3844963 : Nat := 118140960795 + 3844963 * 2 ^ 59
def prefixEnd_3844963 : Nat := 4983230072969 + 3 ^ 40 * 3844963 * 2
def baseEnd_3844963 : Nat := 219368235305927255364427

theorem tailTrace_3844963 : CollatzResearch.WordTrace tailWord_3844963 prefixEnd_3844963 219368235305927255364427 := by
  unfold tailWord_3844963
  simp only [CollatzResearch.WordTrace]
  refine ⟨140237321569363193245547543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93491547712908795497031695 140237321569363193245547543)
  ·
    refine ⟨210355982354044789868321315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140237321569363193245547543 210355982354044789868321315)
    ·
      refine ⟨315533973531067184802481973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210355982354044789868321315 315533973531067184802481973)
      ·
        refine ⟨29581310018537548575232685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315533973531067184802481973 29581310018537548575232685)
        ·
          refine ⟨11092991256951580715712257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29581310018537548575232685 11092991256951580715712257)
          ·
            refine ⟨8319743442713685536784193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11092991256951580715712257 8319743442713685536784193)
            ·
              refine ⟨6239807582035264152588145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8319743442713685536784193 6239807582035264152588145)
              ·
                refine ⟨4679855686526448114441109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239807582035264152588145 4679855686526448114441109)
                ·
                  refine ⟨219368235305927255364427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4679855686526448114441109 219368235305927255364427)
                  ·
                    rfl

theorem cell23_3844963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 6].length) (baseStart_3844963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844963 prefixEnd_3844963 := by exact prefixLift 3844963
  have htrace : WordTrace (prefixWord ++ tailWord_3844963) baseStart_3844963 baseEnd_3844963 := by
    simpa [prefixWord, tailWord_3844963, baseEnd_3844963] using wordTrace_append hprefix tailTrace_3844963
  have hstable : (prefixWord ++ tailWord_3844963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844963).length < 2 ^ (prefixWord ++ tailWord_3844963).sum := by decide
  have hdescent : baseEnd_3844963 < baseStart_3844963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844967 : List Nat := [1, 1, 5, 1, 2, 2, 4, 2, 1, 4]
def baseStart_3844967 : Nat := 118140960795 + 3844967 * 2 ^ 59
def prefixEnd_3844967 : Nat := 4983230072969 + 3 ^ 40 * 3844967 * 2
def baseEnd_3844967 : Nat := 658105390558654427543275

theorem tailTrace_3844967 : CollatzResearch.WordTrace tailWord_3844967 prefixEnd_3844967 658105390558654427543275 := by
  unfold tailWord_3844967
  simp only [CollatzResearch.WordTrace]
  refine ⟨140237467461348701928693155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93491644974232467952462103 140237467461348701928693155)
  ·
    refine ⟨210356201192023052893039733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140237467461348701928693155 210356201192023052893039733)
    ·
      refine ⟨19720893861752161208722475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210356201192023052893039733 19720893861752161208722475)
      ·
        refine ⟨29581340792628241813083713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19720893861752161208722475 29581340792628241813083713)
        ·
          refine ⟨22186005594471181359812785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29581340792628241813083713 22186005594471181359812785)
          ·
            refine ⟨16639504195853386019859589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22186005594471181359812785 16639504195853386019859589)
            ·
              refine ⟨3119907036722509878723673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16639504195853386019859589 3119907036722509878723673)
              ·
                refine ⟨2339930277541882409042755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119907036722509878723673 2339930277541882409042755)
                ·
                  refine ⟨3509895416312823613564133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339930277541882409042755 3509895416312823613564133)
                  ·
                    refine ⟨658105390558654427543275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3509895416312823613564133 658105390558654427543275)
                    ·
                      rfl

theorem cell23_3844967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_3844967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844967 prefixEnd_3844967 := by exact prefixLift 3844967
  have htrace : WordTrace (prefixWord ++ tailWord_3844967) baseStart_3844967 baseEnd_3844967 := by
    simpa [prefixWord, tailWord_3844967, baseEnd_3844967] using wordTrace_append hprefix tailTrace_3844967
  have hstable : (prefixWord ++ tailWord_3844967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844967).length < 2 ^ (prefixWord ++ tailWord_3844967).sum := by decide
  have hdescent : baseEnd_3844967 < baseStart_3844967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844976 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 3, 5]
def baseStart_3844976 : Nat := 118140960795 + 3844976 * 2 ^ 59
def prefixEnd_3844976 : Nat := 4983230072969 + 3 ^ 40 * 3844976 * 2
def baseEnd_3844976 : Nat := 658106931000617915805761

theorem tailTrace_3844976 : CollatzResearch.WordTrace tailWord_3844976 prefixEnd_3844976 658106931000617915805761 := by
  unfold tailWord_3844976
  simp only [CollatzResearch.WordTrace]
  refine ⟨70118897859158048232885391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93491863812210730977180521 70118897859158048232885391)
  ·
    refine ⟨105178346788737072349328087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70118897859158048232885391 105178346788737072349328087)
    ·
      refine ⟨157767520183105608523992131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105178346788737072349328087 157767520183105608523992131)
      ·
        refine ⟨236651280274658412785988197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157767520183105608523992131 236651280274658412785988197)
        ·
          refine ⟨44372115051498452397372787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236651280274658412785988197 44372115051498452397372787)
          ·
            refine ⟨66558172577247678596059181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44372115051498452397372787 66558172577247678596059181)
            ·
              refine ⟨24959314716467879473522193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66558172577247678596059181 24959314716467879473522193)
              ·
                refine ⟨18719486037350909605141645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24959314716467879473522193 18719486037350909605141645)
                ·
                  refine ⟨7019807264006591101928117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18719486037350909605141645 7019807264006591101928117)
                  ·
                    refine ⟨658106931000617915805761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7019807264006591101928117 658106931000617915805761)
                    ·
                      rfl

theorem cell23_3844976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_3844976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844976 prefixEnd_3844976 := by exact prefixLift 3844976
  have htrace : WordTrace (prefixWord ++ tailWord_3844976) baseStart_3844976 baseEnd_3844976 := by
    simpa [prefixWord, tailWord_3844976, baseEnd_3844976] using wordTrace_append hprefix tailTrace_3844976
  have hstable : (prefixWord ++ tailWord_3844976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844976).length < 2 ^ (prefixWord ++ tailWord_3844976).sum := by decide
  have hdescent : baseEnd_3844976 < baseStart_3844976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3844983 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 4, 3, 2]
def baseStart_3844983 : Nat := 118140960795 + 3844983 * 2 ^ 59
def prefixEnd_3844983 : Nat := 4983230072969 + 3 ^ 40 * 3844983 * 2
def baseEnd_3844983 : Nat := 1974324387366435220029751

theorem tailTrace_3844983 : CollatzResearch.WordTrace tailWord_3844983 prefixEnd_3844983 1974324387366435220029751 := by
  unfold tailWord_3844983
  simp only [CollatzResearch.WordTrace]
  refine ⟨140238051029290736661275603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93492034019527157774183735 140238051029290736661275603)
  ·
    refine ⟨210357076543936104991913405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140238051029290736661275603 210357076543936104991913405)
    ·
      refine ⟨78883903703976039371967527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210357076543936104991913405 78883903703976039371967527)
      ·
        refine ⟨118325855555964059057951291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78883903703976039371967527 118325855555964059057951291)
        ·
          refine ⟨177488783333946088586926937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118325855555964059057951291 177488783333946088586926937)
          ·
            refine ⟨133116587500459566440195203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177488783333946088586926937 133116587500459566440195203)
            ·
              refine ⟨199674881250689349660292805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133116587500459566440195203 199674881250689349660292805)
              ·
                refine ⟨37439040234504253061304901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199674881250689349660292805 37439040234504253061304901)
                ·
                  refine ⟨7019820043969547448994669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37439040234504253061304901 7019820043969547448994669)
                  ·
                    refine ⟨2632432516488580293373001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7019820043969547448994669 2632432516488580293373001)
                    ·
                      refine ⟨1974324387366435220029751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632432516488580293373001 1974324387366435220029751)
                      ·
                        rfl

theorem cell23_3844983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_3844983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3844983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3844983 prefixEnd_3844983 := by exact prefixLift 3844983
  have htrace : WordTrace (prefixWord ++ tailWord_3844983) baseStart_3844983 baseEnd_3844983 := by
    simpa [prefixWord, tailWord_3844983, baseEnd_3844983] using wordTrace_append hprefix tailTrace_3844983
  have hstable : (prefixWord ++ tailWord_3844983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3844983).length < 2 ^ (prefixWord ++ tailWord_3844983).sum := by decide
  have hdescent : baseEnd_3844983 < baseStart_3844983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3844983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845000 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_3845000 : Nat := 118140960795 + 3845000 * 2 ^ 59
def prefixEnd_3845000 : Nat := 4983230072969 + 3 ^ 40 * 3845000 * 2
def baseEnd_3845000 : Nat := 1974333116537561653517173

theorem tailTrace_3845000 : CollatzResearch.WordTrace tailWord_3845000 prefixEnd_3845000 1974333116537561653517173 := by
  unfold tailWord_3845000
  simp only [CollatzResearch.WordTrace]
  refine ⟨70119335535114574282322227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93492447380152765709762969 70119335535114574282322227)
  ·
    refine ⟨105179003302671861423483341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70119335535114574282322227 105179003302671861423483341)
    ·
      refine ⟨39442126238501948033806253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105179003302671861423483341 39442126238501948033806253)
      ·
        refine ⟨14790797339438230512677345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39442126238501948033806253 14790797339438230512677345)
        ·
          refine ⟨11093098004578672884508009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14790797339438230512677345 11093098004578672884508009)
          ·
            refine ⟨8319823503434004663381007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093098004578672884508009 8319823503434004663381007)
            ·
              refine ⟨12479735255151006995071511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319823503434004663381007 12479735255151006995071511)
              ·
                refine ⟨18719602882726510492607267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12479735255151006995071511 18719602882726510492607267)
                ·
                  refine ⟨28079404324089765738910901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18719602882726510492607267 28079404324089765738910901)
                  ·
                    refine ⟨2632444155383415538022897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28079404324089765738910901 2632444155383415538022897)
                    ·
                      refine ⟨1974333116537561653517173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632444155383415538022897 1974333116537561653517173)
                      ·
                        rfl

theorem cell23_3845000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_3845000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845000 prefixEnd_3845000 := by exact prefixLift 3845000
  have htrace : WordTrace (prefixWord ++ tailWord_3845000) baseStart_3845000 baseEnd_3845000 := by
    simpa [prefixWord, tailWord_3845000, baseEnd_3845000] using wordTrace_append hprefix tailTrace_3845000
  have hstable : (prefixWord ++ tailWord_3845000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845000).length < 2 ^ (prefixWord ++ tailWord_3845000).sum := by decide
  have hdescent : baseEnd_3845000 < baseStart_3845000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845014 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3845014 : Nat := 118140960795 + 3845014 * 2 ^ 59
def prefixEnd_3845014 : Nat := 4983230072969 + 3 ^ 40 * 3845014 * 2
def baseEnd_3845014 : Nat := 219371145029636066526901

theorem tailTrace_3845014 : CollatzResearch.WordTrace tailWord_3845014 prefixEnd_3845014 219371145029636066526901 := by
  unfold tailWord_3845014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8764948855761151809728381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93492787794785619303769397 8764948855761151809728381)
  ·
    refine ⟨3286855820910431928648143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8764948855761151809728381 3286855820910431928648143)
    ·
      refine ⟨4930283731365647892972215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286855820910431928648143 4930283731365647892972215)
      ·
        refine ⟨7395425597048471839458323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4930283731365647892972215 7395425597048471839458323)
        ·
          refine ⟨11093138395572707759187485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7395425597048471839458323 11093138395572707759187485)
          ·
            refine ⟨4159926898339765409695307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11093138395572707759187485 4159926898339765409695307)
            ·
              refine ⟨6239890347509648114542961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159926898339765409695307 6239890347509648114542961)
              ·
                refine ⟨4679917760632236085907221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239890347509648114542961 4679917760632236085907221)
                ·
                  refine ⟨219371145029636066526901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4679917760632236085907221 219371145029636066526901)
                  ·
                    rfl

theorem cell23_3845014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3845014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845014 prefixEnd_3845014 := by exact prefixLift 3845014
  have htrace : WordTrace (prefixWord ++ tailWord_3845014) baseStart_3845014 baseEnd_3845014 := by
    simpa [prefixWord, tailWord_3845014, baseEnd_3845014] using wordTrace_append hprefix tailTrace_3845014
  have hstable : (prefixWord ++ tailWord_3845014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845014).length < 2 ^ (prefixWord ++ tailWord_3845014).sum := by decide
  have hdescent : baseEnd_3845014 < baseStart_3845014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845050 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3]
def baseStart_3845050 : Nat := 118140960795 + 3845050 * 2 ^ 59
def prefixEnd_3845050 : Nat := 4983230072969 + 3 ^ 40 * 3845050 * 2
def baseEnd_3845050 : Nat := 1974358790570286457891943

theorem tailTrace_3845050 : CollatzResearch.WordTrace tailWord_3845050 prefixEnd_3845050 1974358790570286457891943 := by
  unfold tailWord_3845050
  simp only [CollatzResearch.WordTrace]
  refine ⟨35060123680012001775991151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93493663146698671402643069 35060123680012001775991151)
  ·
    refine ⟨52590185520018002663986727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35060123680012001775991151 52590185520018002663986727)
    ·
      refine ⟨78885278280027003995980091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52590185520018002663986727 78885278280027003995980091)
      ·
        refine ⟨118327917420040505993970137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78885278280027003995980091 118327917420040505993970137)
        ·
          refine ⟨88745938065030379495477603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118327917420040505993970137 88745938065030379495477603)
          ·
            refine ⟨133118907097545569243216405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88745938065030379495477603 133118907097545569243216405)
            ·
              refine ⟨6239948770197448558275769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133118907097545569243216405 6239948770197448558275769)
              ·
                refine ⟨4679961577648086418706827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239948770197448558275769 4679961577648086418706827)
                ·
                  refine ⟨7019942366472129628060241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679961577648086418706827 7019942366472129628060241)
                  ·
                    refine ⟨5264956774854097221045181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7019942366472129628060241 5264956774854097221045181)
                    ·
                      refine ⟨1974358790570286457891943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5264956774854097221045181 1974358790570286457891943)
                      ·
                        rfl

theorem cell23_3845050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_3845050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845050 prefixEnd_3845050 := by exact prefixLift 3845050
  have htrace : WordTrace (prefixWord ++ tailWord_3845050) baseStart_3845050 baseEnd_3845050 := by
    simpa [prefixWord, tailWord_3845050, baseEnd_3845050] using wordTrace_append hprefix tailTrace_3845050
  have hstable : (prefixWord ++ tailWord_3845050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845050).length < 2 ^ (prefixWord ++ tailWord_3845050).sum := by decide
  have hdescent : baseEnd_3845050 < baseStart_3845050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845053 : List Nat := [1, 4, 1, 2, 4, 1, 1, 9]
def baseStart_3845053 : Nat := 118140960795 + 3845053 * 2 ^ 59
def prefixEnd_3845053 : Nat := 4983230072969 + 3 ^ 40 * 3845053 * 2
def baseEnd_3845053 : Nat := 73124456704157405413127

theorem tailTrace_3845053 : CollatzResearch.WordTrace tailWord_3845053 prefixEnd_3845053 73124456704157405413127 := by
  unfold tailWord_3845053
  simp only [CollatzResearch.WordTrace]
  refine ⟨140240604139037138616323813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93493736092691425744215875 140240604139037138616323813)
  ·
    refine ⟨26295113276069463490560715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140240604139037138616323813 26295113276069463490560715)
    ·
      refine ⟨39442669914104195235841073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26295113276069463490560715 39442669914104195235841073)
      ·
        refine ⟨29582002435578146426880805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39442669914104195235841073 29582002435578146426880805)
        ·
          refine ⟨5546625456670902455040151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29582002435578146426880805 5546625456670902455040151)
          ·
            refine ⟨8319938185006353682560227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5546625456670902455040151 8319938185006353682560227)
            ·
              refine ⟨12479907277509530523840341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319938185006353682560227 12479907277509530523840341)
              ·
                refine ⟨73124456704157405413127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12479907277509530523840341 73124456704157405413127)
                ·
                  rfl

theorem cell23_3845053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 9].length) (baseStart_3845053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845053 prefixEnd_3845053 := by exact prefixLift 3845053
  have htrace : WordTrace (prefixWord ++ tailWord_3845053) baseStart_3845053 baseEnd_3845053 := by
    simpa [prefixWord, tailWord_3845053, baseEnd_3845053] using wordTrace_append hprefix tailTrace_3845053
  have hstable : (prefixWord ++ tailWord_3845053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845053).length < 2 ^ (prefixWord ++ tailWord_3845053).sum := by decide
  have hdescent : baseEnd_3845053 < baseStart_3845053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845063 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_3845063 : Nat := 118140960795 + 3845063 * 2 ^ 59
def prefixEnd_3845063 : Nat := 4983230072969 + 3 ^ 40 * 3845063 * 2
def baseEnd_3845063 : Nat := 1974365465818794907029383

theorem tailTrace_3845063 : CollatzResearch.WordTrace tailWord_3845063 prefixEnd_3845063 1974365465818794907029383 := by
  unfold tailWord_3845063
  simp only [CollatzResearch.WordTrace]
  refine ⟨140240968869000910324187843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93493979246000606882791895 140240968869000910324187843)
  ·
    refine ⟨210361453303501365486281765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140240968869000910324187843 210361453303501365486281765)
    ·
      refine ⟨39442772494406506028677831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210361453303501365486281765 39442772494406506028677831)
      ·
        refine ⟨59164158741609759043016747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39442772494406506028677831 59164158741609759043016747)
        ·
          refine ⟨88746238112414638564525121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59164158741609759043016747 88746238112414638564525121)
          ·
            refine ⟨66559678584310978923393841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88746238112414638564525121 66559678584310978923393841)
            ·
              refine ⟨49919758938233234192545381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66559678584310978923393841 49919758938233234192545381)
              ·
                refine ⟨9359954800918731411102259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49919758938233234192545381 9359954800918731411102259)
                ·
                  refine ⟨14039932201378097116653389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359954800918731411102259 14039932201378097116653389)
                  ·
                    refine ⟨5264974575516786418745021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14039932201378097116653389 5264974575516786418745021)
                    ·
                      refine ⟨1974365465818794907029383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5264974575516786418745021 1974365465818794907029383)
                      ·
                        rfl

theorem cell23_3845063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_3845063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845063 prefixEnd_3845063 := by exact prefixLift 3845063
  have htrace : WordTrace (prefixWord ++ tailWord_3845063) baseStart_3845063 baseEnd_3845063 := by
    simpa [prefixWord, tailWord_3845063, baseEnd_3845063] using wordTrace_append hprefix tailTrace_3845063
  have hstable : (prefixWord ++ tailWord_3845063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845063).length < 2 ^ (prefixWord ++ tailWord_3845063).sum := by decide
  have hdescent : baseEnd_3845063 < baseStart_3845063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845066 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_3845066 : Nat := 118140960795 + 3845066 * 2 ^ 59
def prefixEnd_3845066 : Nat := 4983230072969 + 3 ^ 40 * 3845066 * 2
def baseEnd_3845066 : Nat := 658122335420252798430623

theorem tailTrace_3845066 : CollatzResearch.WordTrace tailWord_3845066 prefixEnd_3845066 658122335420252798430623 := by
  unfold tailWord_3845066
  simp only [CollatzResearch.WordTrace]
  refine ⟨35060269571997510459136763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93494052191993361224364701 35060269571997510459136763)
  ·
    refine ⟨52590404357996265688705145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35060269571997510459136763 52590404357996265688705145)
    ·
      refine ⟨39442803268497199266528859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52590404357996265688705145 39442803268497199266528859)
      ·
        refine ⟨59164204902745798899793289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39442803268497199266528859 59164204902745798899793289)
        ·
          refine ⟨44373153677059349174844967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59164204902745798899793289 44373153677059349174844967)
          ·
            refine ⟨66559730515589023762267451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44373153677059349174844967 66559730515589023762267451)
            ·
              refine ⟨99839595773383535643401177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66559730515589023762267451 99839595773383535643401177)
              ·
                refine ⟨74879696830037651732550883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99839595773383535643401177 74879696830037651732550883)
                ·
                  refine ⟨112319545245056477598826325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74879696830037651732550883 112319545245056477598826325)
                  ·
                    refine ⟨658122335420252798430623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 112319545245056477598826325 658122335420252798430623)
                    ·
                      rfl

theorem cell23_3845066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_3845066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845066 prefixEnd_3845066 := by exact prefixLift 3845066
  have htrace : WordTrace (prefixWord ++ tailWord_3845066) baseStart_3845066 baseEnd_3845066 := by
    simpa [prefixWord, tailWord_3845066, baseEnd_3845066] using wordTrace_append hprefix tailTrace_3845066
  have hstable : (prefixWord ++ tailWord_3845066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845066).length < 2 ^ (prefixWord ++ tailWord_3845066).sum := by decide
  have hdescent : baseEnd_3845066 < baseStart_3845066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845080 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 4, 1, 3]
def baseStart_3845080 : Nat := 118140960795 + 3845080 * 2 ^ 59
def prefixEnd_3845080 : Nat := 4983230072969 + 3 ^ 40 * 3845080 * 2
def baseEnd_3845080 : Nat := 1974374194989921340516805

theorem tailTrace_3845080 : CollatzResearch.WordTrace tailWord_3845080 prefixEnd_3845080 1974374194989921340516805 := by
  unfold tailWord_3845080
  simp only [CollatzResearch.WordTrace]
  refine ⟨70120794454969661113778347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93494392606626214818371129 70120794454969661113778347)
  ·
    refine ⟨105181191682454491670667521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70120794454969661113778347 105181191682454491670667521)
    ·
      refine ⟨78885893761840868753000641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105181191682454491670667521 78885893761840868753000641)
      ·
        refine ⟨59164420321380651564750481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78885893761840868753000641 59164420321380651564750481)
        ·
          refine ⟨44373315241035488673562861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59164420321380651564750481 44373315241035488673562861)
          ·
            refine ⟨16639993215388308252586073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44373315241035488673562861 16639993215388308252586073)
            ·
              refine ⟨12479994911541231189439555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16639993215388308252586073 12479994911541231189439555)
              ·
                refine ⟨18719992367311846784159333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12479994911541231189439555 18719992367311846784159333)
                ·
                  refine ⟨3509998568870971272029875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18719992367311846784159333 3509998568870971272029875)
                  ·
                    refine ⟨5264997853306456908044813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3509998568870971272029875 5264997853306456908044813)
                    ·
                      refine ⟨1974374194989921340516805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5264997853306456908044813 1974374194989921340516805)
                      ·
                        rfl

theorem cell23_3845080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_3845080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845080 prefixEnd_3845080 := by exact prefixLift 3845080
  have htrace : WordTrace (prefixWord ++ tailWord_3845080) baseStart_3845080 baseEnd_3845080 := by
    simpa [prefixWord, tailWord_3845080, baseEnd_3845080] using wordTrace_append hprefix tailTrace_3845080
  have hstable : (prefixWord ++ tailWord_3845080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845080).length < 2 ^ (prefixWord ++ tailWord_3845080).sum := by decide
  have hdescent : baseEnd_3845080 < baseStart_3845080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845081 : List Nat := [1, 2, 1, 2, 5, 2, 3, 2, 1, 2, 2]
def baseStart_3845081 : Nat := 118140960795 + 3845081 * 2 ^ 59
def prefixEnd_3845081 : Nat := 4983230072969 + 3 ^ 40 * 3845081 * 2
def baseEnd_3845081 : Nat := 1974374708470575836604301

theorem tailTrace_3845081 : CollatzResearch.WordTrace tailWord_3845081 prefixEnd_3845081 1974374708470575836604301 := by
  unfold tailWord_3845081
  simp only [CollatzResearch.WordTrace]
  refine ⟨140241625382935699398343097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93494416921957132932228731 140241625382935699398343097)
  ·
    refine ⟨105181219037201774548757323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140241625382935699398343097 105181219037201774548757323)
    ·
      refine ⟨157771828555802661823135985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105181219037201774548757323 157771828555802661823135985)
      ·
        refine ⟨118328871416851996367351989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157771828555802661823135985 118328871416851996367351989)
        ·
          refine ⟨11093331695329874659439249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118328871416851996367351989 11093331695329874659439249)
          ·
            refine ⟨8319998771497405994579437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093331695329874659439249 8319998771497405994579437)
            ·
              refine ⟨3119999539311527247967289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8319998771497405994579437 3119999539311527247967289)
              ·
                refine ⟨2339999654483645435975467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119999539311527247967289 2339999654483645435975467)
                ·
                  refine ⟨3509999481725468153963201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339999654483645435975467 3509999481725468153963201)
                  ·
                    refine ⟨2632499611294101115472401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3509999481725468153963201 2632499611294101115472401)
                    ·
                      refine ⟨1974374708470575836604301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632499611294101115472401 1974374708470575836604301)
                      ·
                        rfl

theorem cell23_3845081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 2, 2].length) (baseStart_3845081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845081 prefixEnd_3845081 := by exact prefixLift 3845081
  have htrace : WordTrace (prefixWord ++ tailWord_3845081) baseStart_3845081 baseEnd_3845081 := by
    simpa [prefixWord, tailWord_3845081, baseEnd_3845081] using wordTrace_append hprefix tailTrace_3845081
  have hstable : (prefixWord ++ tailWord_3845081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845081).length < 2 ^ (prefixWord ++ tailWord_3845081).sum := by decide
  have hdescent : baseEnd_3845081 < baseStart_3845081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845154 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_3845154 : Nat := 118140960795 + 3845154 * 2 ^ 59
def prefixEnd_3845154 : Nat := 4983230072969 + 3 ^ 40 * 3845154 * 2
def baseEnd_3845154 : Nat := 1974412192558354050991465

theorem tailTrace_3845154 : CollatzResearch.WordTrace tailWord_3845154 prefixEnd_3845154 1974412192558354050991465 := by
  unfold tailWord_3845154
  simp only [CollatzResearch.WordTrace]
  refine ⟨35061071977917808216437629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93496191941114155243833677 35061071977917808216437629)
  ·
    refine ⟨13147901991719178081164111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35061071977917808216437629 13147901991719178081164111)
    ·
      refine ⟨19721852987578767121746167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13147901991719178081164111 19721852987578767121746167)
      ·
        refine ⟨29582779481368150682619251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19721852987578767121746167 29582779481368150682619251)
        ·
          refine ⟨44374169222052226023928877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29582779481368150682619251 44374169222052226023928877)
          ·
            refine ⟨16640313458269584758973329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44374169222052226023928877 16640313458269584758973329)
            ·
              refine ⟨12480235093702188569229997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16640313458269584758973329 12480235093702188569229997)
              ·
                refine ⟨4680088160138320713461249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12480235093702188569229997 4680088160138320713461249)
                ·
                  refine ⟨3510066120103740535095937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4680088160138320713461249 3510066120103740535095937)
                  ·
                    refine ⟨2632549590077805401321953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3510066120103740535095937 2632549590077805401321953)
                    ·
                      refine ⟨1974412192558354050991465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632549590077805401321953 1974412192558354050991465)
                      ·
                        rfl

theorem cell23_3845154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_3845154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845154 prefixEnd_3845154 := by exact prefixLift 3845154
  have htrace : WordTrace (prefixWord ++ tailWord_3845154) baseStart_3845154 baseEnd_3845154 := by
    simpa [prefixWord, tailWord_3845154, baseEnd_3845154] using wordTrace_append hprefix tailTrace_3845154
  have hstable : (prefixWord ++ tailWord_3845154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845154).length < 2 ^ (prefixWord ++ tailWord_3845154).sum := by decide
  have hdescent : baseEnd_3845154 < baseStart_3845154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845177 : List Nat := [1, 2, 1, 5, 2, 2, 2, 3, 5]
def baseStart_3845177 : Nat := 118140960795 + 3845177 * 2 ^ 59
def prefixEnd_3845177 : Nat := 4983230072969 + 3 ^ 40 * 3845177 * 2
def baseEnd_3845177 : Nat := 219380444734823051222651

theorem tailTrace_3845177 : CollatzResearch.WordTrace tailWord_3845177 prefixEnd_3845177 219380444734823051222651 := by
  unfold tailWord_3845177
  simp only [CollatzResearch.WordTrace]
  refine ⟨140245126790587907793837785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93496751193725271862558523 140245126790587907793837785)
  ·
    refine ⟨105183845092940930845378339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140245126790587907793837785 105183845092940930845378339)
    ·
      refine ⟨157775767639411396268067509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105183845092940930845378339 157775767639411396268067509)
      ·
        refine ⟨14791478216194818400131329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157775767639411396268067509 14791478216194818400131329)
        ·
          refine ⟨11093608662146113800098497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14791478216194818400131329 11093608662146113800098497)
          ·
            refine ⟨8320206496609585350073873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093608662146113800098497 8320206496609585350073873)
            ·
              refine ⟨6240154872457189012555405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8320206496609585350073873 6240154872457189012555405)
              ·
                refine ⟨2340058077171445879708277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6240154872457189012555405 2340058077171445879708277)
                ·
                  refine ⟨219380444734823051222651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2340058077171445879708277 219380444734823051222651)
                  ·
                    rfl

theorem cell23_3845177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 5].length) (baseStart_3845177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845177 prefixEnd_3845177 := by exact prefixLift 3845177
  have htrace : WordTrace (prefixWord ++ tailWord_3845177) baseStart_3845177 baseEnd_3845177 := by
    simpa [prefixWord, tailWord_3845177, baseEnd_3845177] using wordTrace_append hprefix tailTrace_3845177
  have hstable : (prefixWord ++ tailWord_3845177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845177).length < 2 ^ (prefixWord ++ tailWord_3845177).sum := by decide
  have hdescent : baseEnd_3845177 < baseStart_3845177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845210 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2]
def baseStart_3845210 : Nat := 118140960795 + 3845210 * 2 ^ 59
def prefixEnd_3845210 : Nat := 4983230072969 + 3 ^ 40 * 3845210 * 2
def baseEnd_3845210 : Nat := 1974440947475005831891207

theorem tailTrace_3845210 : CollatzResearch.WordTrace tailWord_3845210 prefixEnd_3845210 1974440947475005831891207 := by
  unfold tailWord_3845210
  simp only [CollatzResearch.WordTrace]
  refine ⟨35061582599867088607447271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93497553599645569619859389 35061582599867088607447271)
  ·
    refine ⟨52592373899800632911170907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35061582599867088607447271 52592373899800632911170907)
    ·
      refine ⟨78888560849700949366756361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52592373899800632911170907 78888560849700949366756361)
      ·
        refine ⟨59166420637275712025067271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78888560849700949366756361 59166420637275712025067271)
        ·
          refine ⟨88749630955913568037600907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59166420637275712025067271 88749630955913568037600907)
          ·
            refine ⟨133124446433870352056401361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88749630955913568037600907 133124446433870352056401361)
            ·
              refine ⟨99843334825402764042301021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133124446433870352056401361 99843334825402764042301021)
              ·
                refine ⟨37441250559526036515862883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99843334825402764042301021 37441250559526036515862883)
                ·
                  refine ⟨56161875839289054773794325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37441250559526036515862883 56161875839289054773794325)
                  ·
                    refine ⟨2632587929966674442521609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56161875839289054773794325 2632587929966674442521609)
                    ·
                      refine ⟨1974440947475005831891207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632587929966674442521609 1974440947475005831891207)
                      ·
                        rfl

theorem cell23_3845210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_3845210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845210 prefixEnd_3845210 := by exact prefixLift 3845210
  have htrace : WordTrace (prefixWord ++ tailWord_3845210) baseStart_3845210 baseEnd_3845210 := by
    simpa [prefixWord, tailWord_3845210, baseEnd_3845210] using wordTrace_append hprefix tailTrace_3845210
  have hstable : (prefixWord ++ tailWord_3845210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845210).length < 2 ^ (prefixWord ++ tailWord_3845210).sum := by decide
  have hdescent : baseEnd_3845210 < baseStart_3845210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845277 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_3845277 : Nat := 118140960795 + 3845277 * 2 ^ 59
def prefixEnd_3845277 : Nat := 4983230072969 + 3 ^ 40 * 3845277 * 2
def baseEnd_3845277 : Nat := 1974475350678857069753399

theorem tailTrace_3845277 : CollatzResearch.WordTrace tailWord_3845277 prefixEnd_3845277 1974475350678857069753399 := by
  unfold tailWord_3845277
  simp only [CollatzResearch.WordTrace]
  refine ⟨140248774090225624872478085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93499182726817083248318723 140248774090225624872478085)
  ·
    refine ⟨26296645141917304663589641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140248774090225624872478085 26296645141917304663589641)
    ·
      refine ⟨19722483856437978497692231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26296645141917304663589641 19722483856437978497692231)
      ·
        refine ⟨29583725784656967746538347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19722483856437978497692231 29583725784656967746538347)
        ·
          refine ⟨44375588676985451619807521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29583725784656967746538347 44375588676985451619807521)
          ·
            refine ⟨33281691507739088714855641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44375588676985451619807521 33281691507739088714855641)
            ·
              refine ⟨24961268630804316536141731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33281691507739088714855641 24961268630804316536141731)
              ·
                refine ⟨37441902946206474804212597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24961268630804316536141731 37441902946206474804212597)
                ·
                  refine ⟨3510178401206857012894931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37441902946206474804212597 3510178401206857012894931)
                  ·
                    refine ⟨5265267601810285519342397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3510178401206857012894931 5265267601810285519342397)
                    ·
                      refine ⟨1974475350678857069753399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5265267601810285519342397 1974475350678857069753399)
                      ·
                        rfl

theorem cell23_3845277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_3845277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845277 prefixEnd_3845277 := by exact prefixLift 3845277
  have htrace : WordTrace (prefixWord ++ tailWord_3845277) baseStart_3845277 baseEnd_3845277 := by
    simpa [prefixWord, tailWord_3845277, baseEnd_3845277] using wordTrace_append hprefix tailTrace_3845277
  have hstable : (prefixWord ++ tailWord_3845277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845277).length < 2 ^ (prefixWord ++ tailWord_3845277).sum := by decide
  have hdescent : baseEnd_3845277 < baseStart_3845277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845280 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 3, 5]
def baseStart_3845280 : Nat := 118140960795 + 3845280 * 2 ^ 59
def prefixEnd_3845280 : Nat := 4983230072969 + 3 ^ 40 * 3845280 * 2
def baseEnd_3845280 : Nat := 658158963706940186005295

theorem tailTrace_3845280 : CollatzResearch.WordTrace tailWord_3845280 prefixEnd_3845280 658158963706940186005295 := by
  unfold tailWord_3845280
  simp only [CollatzResearch.WordTrace]
  refine ⟨70124441754607378192418647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93499255672809837589891529 70124441754607378192418647)
  ·
    refine ⟨105186662631911067288627971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70124441754607378192418647 105186662631911067288627971)
    ·
      refine ⟨157779993947866600932941957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105186662631911067288627971 157779993947866600932941957)
      ·
        refine ⟨29583748865224987674926617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157779993947866600932941957 29583748865224987674926617)
        ·
          refine ⟨22187811648918740756194963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29583748865224987674926617 22187811648918740756194963)
          ·
            refine ⟨33281717473378111134292445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22187811648918740756194963 33281717473378111134292445)
            ·
              refine ⟨12480644052516791675359667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33281717473378111134292445 12480644052516791675359667)
              ·
                refine ⟨18720966078775187513039501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12480644052516791675359667 18720966078775187513039501)
                ·
                  refine ⟨7020362279540695317389813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18720966078775187513039501 7020362279540695317389813)
                  ·
                    refine ⟨658158963706940186005295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7020362279540695317389813 658158963706940186005295)
                    ·
                      rfl

theorem cell23_3845280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_3845280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845280 prefixEnd_3845280 := by exact prefixLift 3845280
  have htrace : WordTrace (prefixWord ++ tailWord_3845280) baseStart_3845280 baseEnd_3845280 := by
    simpa [prefixWord, tailWord_3845280, baseEnd_3845280] using wordTrace_append hprefix tailTrace_3845280
  have hstable : (prefixWord ++ tailWord_3845280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845280).length < 2 ^ (prefixWord ++ tailWord_3845280).sum := by decide
  have hdescent : baseEnd_3845280 < baseStart_3845280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845311 : List Nat := [1, 1, 2, 2, 2, 2, 6, 2, 1, 1, 3]
def baseStart_3845311 : Nat := 118140960795 + 3845311 * 2 ^ 59
def prefixEnd_3845311 : Nat := 4983230072969 + 3 ^ 40 * 3845311 * 2
def baseEnd_3845311 : Nat := 1974492809021109936728243

theorem tailTrace_3845311 : CollatzResearch.WordTrace tailWord_3845311 prefixEnd_3845311 1974492809021109936728243 := by
  unfold tailWord_3845311
  simp only [CollatzResearch.WordTrace]
  refine ⟨140250014172102448679215787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93500009448068299119477191 140250014172102448679215787)
  ·
    refine ⟨210375021258153673018823681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140250014172102448679215787 210375021258153673018823681)
    ·
      refine ⟨157781265943615254764117761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210375021258153673018823681 157781265943615254764117761)
      ·
        refine ⟨118335949457711441073088321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157781265943615254764117761 118335949457711441073088321)
        ·
          refine ⟨88751962093283580804816241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118335949457711441073088321 88751962093283580804816241)
          ·
            refine ⟨66563971569962685603612181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88751962093283580804816241 66563971569962685603612181)
            ·
              refine ⟨3120186167342000887669321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66563971569962685603612181 3120186167342000887669321)
              ·
                refine ⟨2340139625506500665751991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120186167342000887669321 2340139625506500665751991)
                ·
                  refine ⟨3510209438259750998627987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340139625506500665751991 3510209438259750998627987)
                  ·
                    refine ⟨5265314157389626497941981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3510209438259750998627987 5265314157389626497941981)
                    ·
                      refine ⟨1974492809021109936728243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5265314157389626497941981 1974492809021109936728243)
                      ·
                        rfl

theorem cell23_3845311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 1, 1, 3].length) (baseStart_3845311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845311 prefixEnd_3845311 := by exact prefixLift 3845311
  have htrace : WordTrace (prefixWord ++ tailWord_3845311) baseStart_3845311 baseEnd_3845311 := by
    simpa [prefixWord, tailWord_3845311, baseEnd_3845311] using wordTrace_append hprefix tailTrace_3845311
  have hstable : (prefixWord ++ tailWord_3845311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845311).length < 2 ^ (prefixWord ++ tailWord_3845311).sum := by decide
  have hdescent : baseEnd_3845311 < baseStart_3845311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845320 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_3845320 : Nat := 118140960795 + 3845320 * 2 ^ 59
def prefixEnd_3845320 : Nat := 4983230072969 + 3 ^ 40 * 3845320 * 2
def baseEnd_3845320 : Nat := 1974497430347000401515701

theorem tailTrace_3845320 : CollatzResearch.WordTrace tailWord_3845320 prefixEnd_3845320 1974497430347000401515701 := by
  unfold tailWord_3845320
  simp only [CollatzResearch.WordTrace]
  refine ⟨70125171214534921608146707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93500228286046562144195609 70125171214534921608146707)
  ·
    refine ⟨105187756821802382412220061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70125171214534921608146707 105187756821802382412220061)
    ·
      refine ⟨39445408808175893404582523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105187756821802382412220061 39445408808175893404582523)
      ·
        refine ⟨59168113212263840106873785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39445408808175893404582523 59168113212263840106873785)
        ·
          refine ⟨44376084909197880080155339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59168113212263840106873785 44376084909197880080155339)
          ·
            refine ⟨66564127363796820120233009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44376084909197880080155339 66564127363796820120233009)
            ·
              refine ⟨49923095522847615090174757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66564127363796820120233009 49923095522847615090174757)
              ·
                refine ⟨9360580410533927829407767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49923095522847615090174757 9360580410533927829407767)
                ·
                  refine ⟨14040870615800891744111651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9360580410533927829407767 14040870615800891744111651)
                  ·
                    refine ⟨21061305923701337616167477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14040870615800891744111651 21061305923701337616167477)
                    ·
                      refine ⟨1974497430347000401515701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21061305923701337616167477 1974497430347000401515701)
                      ·
                        rfl

theorem cell23_3845320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_3845320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845320 prefixEnd_3845320 := by exact prefixLift 3845320
  have htrace : WordTrace (prefixWord ++ tailWord_3845320) baseStart_3845320 baseEnd_3845320 := by
    simpa [prefixWord, tailWord_3845320, baseEnd_3845320] using wordTrace_append hprefix tailTrace_3845320
  have hstable : (prefixWord ++ tailWord_3845320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845320).length < 2 ^ (prefixWord ++ tailWord_3845320).sum := by decide
  have hdescent : baseEnd_3845320 < baseStart_3845320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845323 : List Nat := [1, 1, 1, 1, 3, 2, 2, 12]
def baseStart_3845323 : Nat := 118140960795 + 3845323 * 2 ^ 59
def prefixEnd_3845323 : Nat := 4983230072969 + 3 ^ 40 * 3845323 * 2
def baseEnd_3845323 : Nat := 73129591510702366288081

theorem tailTrace_3845323 : CollatzResearch.WordTrace tailWord_3845323 prefixEnd_3845323 73129591510702366288081 := by
  unfold tailWord_3845323
  simp only [CollatzResearch.WordTrace]
  refine ⟨140250451848058974728652623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93500301232039316485768415 140250451848058974728652623)
  ·
    refine ⟨210375677772088462092978935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140250451848058974728652623 210375677772088462092978935)
    ·
      refine ⟨315563516658132693139468403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210375677772088462092978935 315563516658132693139468403)
      ·
        refine ⟨473345274987199039709202605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315563516658132693139468403 473345274987199039709202605)
        ·
          refine ⟨177504478120199639890950977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473345274987199039709202605 177504478120199639890950977)
          ·
            refine ⟨133128358590149729918213233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177504478120199639890950977 133128358590149729918213233)
            ·
              refine ⟨99846268942612297438659925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133128358590149729918213233 99846268942612297438659925)
              ·
                refine ⟨73129591510702366288081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 99846268942612297438659925 73129591510702366288081)
                ·
                  rfl

theorem cell23_3845323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 12].length) (baseStart_3845323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845323 prefixEnd_3845323 := by exact prefixLift 3845323
  have htrace : WordTrace (prefixWord ++ tailWord_3845323) baseStart_3845323 baseEnd_3845323 := by
    simpa [prefixWord, tailWord_3845323, baseEnd_3845323] using wordTrace_append hprefix tailTrace_3845323
  have hstable : (prefixWord ++ tailWord_3845323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845323).length < 2 ^ (prefixWord ++ tailWord_3845323).sum := by decide
  have hdescent : baseEnd_3845323 < baseStart_3845323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845337 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 3]
def baseStart_3845337 : Nat := 118140960795 + 3845337 * 2 ^ 59
def prefixEnd_3845337 : Nat := 4983230072969 + 3 ^ 40 * 3845337 * 2
def baseEnd_3845337 : Nat := 1974506159518126835003123

theorem tailTrace_3845337 : CollatzResearch.WordTrace tailWord_3845337 prefixEnd_3845337 1974506159518126835003123 := by
  unfold tailWord_3845337
  simp only [CollatzResearch.WordTrace]
  refine ⟨140250962470008255119662265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93500641646672170079774843 140250962470008255119662265)
  ·
    refine ⟨105188221852506191339746699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140250962470008255119662265 105188221852506191339746699)
    ·
      refine ⟨157782332778759287009620049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105188221852506191339746699 157782332778759287009620049)
      ·
        refine ⟨118336749584069465257215037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157782332778759287009620049 118336749584069465257215037)
        ·
          refine ⟨44376281094026049471455639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118336749584069465257215037 44376281094026049471455639)
          ·
            refine ⟨66564421641039074207183459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44376281094026049471455639 66564421641039074207183459)
            ·
              refine ⟨99846632461558611310775189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66564421641039074207183459 99846632461558611310775189)
              ·
                refine ⟨4680310896635559905192587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99846632461558611310775189 4680310896635559905192587)
                ·
                  refine ⟨7020466344953339857788881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680310896635559905192587 7020466344953339857788881)
                  ·
                    refine ⟨5265349758715004893341661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7020466344953339857788881 5265349758715004893341661)
                    ·
                      refine ⟨1974506159518126835003123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5265349758715004893341661 1974506159518126835003123)
                      ·
                        rfl

theorem cell23_3845337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_3845337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845337 prefixEnd_3845337 := by exact prefixLift 3845337
  have htrace : WordTrace (prefixWord ++ tailWord_3845337) baseStart_3845337 baseEnd_3845337 := by
    simpa [prefixWord, tailWord_3845337, baseEnd_3845337] using wordTrace_append hprefix tailTrace_3845337
  have hstable : (prefixWord ++ tailWord_3845337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845337).length < 2 ^ (prefixWord ++ tailWord_3845337).sum := by decide
  have hdescent : baseEnd_3845337 < baseStart_3845337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845354 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_3845354 : Nat := 118140960795 + 3845354 * 2 ^ 59
def prefixEnd_3845354 : Nat := 4983230072969 + 3 ^ 40 * 3845354 * 2
def baseEnd_3845354 : Nat := 1974514888689253268490545

theorem tailTrace_3845354 : CollatzResearch.WordTrace tailWord_3845354 prefixEnd_3845354 1974514888689253268490545 := by
  unfold tailWord_3845354
  simp only [CollatzResearch.WordTrace]
  refine ⟨35062895627736666755757779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93501055007297778015354077 35062895627736666755757779)
  ·
    refine ⟨52594343441605000133636669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35062895627736666755757779 52594343441605000133636669)
    ·
      refine ⟨19722878790601875050113751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52594343441605000133636669 19722878790601875050113751)
      ·
        refine ⟨29584318185902812575170627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19722878790601875050113751 29584318185902812575170627)
        ·
          refine ⟨44376477278854218862755941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29584318185902812575170627 44376477278854218862755941)
          ·
            refine ⟨8320589489785166036766739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44376477278854218862755941 8320589489785166036766739)
            ·
              refine ⟨12480884234677749055150109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8320589489785166036766739 12480884234677749055150109)
              ·
                refine ⟨4680331588004155895681291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12480884234677749055150109 4680331588004155895681291)
                ·
                  refine ⟨7020497382006233843521937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680331588004155895681291 7020497382006233843521937)
                  ·
                    refine ⟨5265373036504675382641453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7020497382006233843521937 5265373036504675382641453)
                    ·
                      refine ⟨1974514888689253268490545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5265373036504675382641453 1974514888689253268490545)
                      ·
                        rfl

theorem cell23_3845354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_3845354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845354 prefixEnd_3845354 := by exact prefixLift 3845354
  have htrace : WordTrace (prefixWord ++ tailWord_3845354) baseStart_3845354 baseEnd_3845354 := by
    simpa [prefixWord, tailWord_3845354, baseEnd_3845354] using wordTrace_append hprefix tailTrace_3845354
  have hstable : (prefixWord ++ tailWord_3845354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845354).length < 2 ^ (prefixWord ++ tailWord_3845354).sum := by decide
  have hdescent : baseEnd_3845354 < baseStart_3845354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845367 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 3]
def baseStart_3845367 : Nat := 118140960795 + 3845367 * 2 ^ 59
def prefixEnd_3845367 : Nat := 4983230072969 + 3 ^ 40 * 3845367 * 2
def baseEnd_3845367 : Nat := 1974521563937761717627985

theorem tailTrace_3845367 : CollatzResearch.WordTrace tailWord_3845367 prefixEnd_3845367 1974521563937761717627985 := by
  unfold tailWord_3845367
  simp only [CollatzResearch.WordTrace]
  refine ⟨140252056659899570243254355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93501371106599713495502903 140252056659899570243254355)
  ·
    refine ⟨210378084989849355364881533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140252056659899570243254355 210378084989849355364881533)
    ·
      refine ⟨78891781871193508261830575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210378084989849355364881533 78891781871193508261830575)
      ·
        refine ⟨118337672806790262392745863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78891781871193508261830575 118337672806790262392745863)
        ·
          refine ⟨177506509210185393589118795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118337672806790262392745863 177506509210185393589118795)
          ·
            refine ⟨266259763815278090383678193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177506509210185393589118795 266259763815278090383678193)
            ·
              refine ⟨199694822861458567787758645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266259763815278090383678193 199694822861458567787758645)
              ·
                refine ⟨18721389643261740730102373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199694822861458567787758645 18721389643261740730102373)
                ·
                  refine ⟨3510260558111576386894195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18721389643261740730102373 3510260558111576386894195)
                  ·
                    refine ⟨5265390837167364580341293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3510260558111576386894195 5265390837167364580341293)
                    ·
                      refine ⟨1974521563937761717627985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5265390837167364580341293 1974521563937761717627985)
                      ·
                        rfl

theorem cell23_3845367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_3845367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845367 prefixEnd_3845367 := by exact prefixLift 3845367
  have htrace : WordTrace (prefixWord ++ tailWord_3845367) baseStart_3845367 baseEnd_3845367 := by
    simpa [prefixWord, tailWord_3845367, baseEnd_3845367] using wordTrace_append hprefix tailTrace_3845367
  have hstable : (prefixWord ++ tailWord_3845367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845367).length < 2 ^ (prefixWord ++ tailWord_3845367).sum := by decide
  have hdescent : baseEnd_3845367 < baseStart_3845367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845378 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_3845378 : Nat := 118140960795 + 3845378 * 2 ^ 59
def prefixEnd_3845378 : Nat := 4983230072969 + 3 ^ 40 * 3845378 * 2
def baseEnd_3845378 : Nat := 658175737408320391530145

theorem tailTrace_3845378 : CollatzResearch.WordTrace tailWord_3845378 prefixEnd_3845378 658175737408320391530145 := by
  unfold tailWord_3845378
  simp only [CollatzResearch.WordTrace]
  refine ⟨35063114465714929780476197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93501638575239812747936525 35063114465714929780476197)
  ·
    refine ⟨6574333962321549333839287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35063114465714929780476197 6574333962321549333839287)
    ·
      refine ⟨9861500943482324000758931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6574333962321549333839287 9861500943482324000758931)
      ·
        refine ⟨14792251415223486001138397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9861500943482324000758931 14792251415223486001138397)
        ·
          refine ⟨5547094280708807250426899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14792251415223486001138397 5547094280708807250426899)
          ·
            refine ⟨8320641421063210875640349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547094280708807250426899 8320641421063210875640349)
            ·
              refine ⟨3120240532898704078365131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8320641421063210875640349 3120240532898704078365131)
              ·
                refine ⟨4680360799348056117547697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120240532898704078365131 4680360799348056117547697)
                ·
                  refine ⟨3510270599511042088160773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4680360799348056117547697 3510270599511042088160773)
                  ·
                    refine ⟨658175737408320391530145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3510270599511042088160773 658175737408320391530145)
                    ·
                      rfl

theorem cell23_3845378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_3845378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845378 prefixEnd_3845378 := by exact prefixLift 3845378
  have htrace : WordTrace (prefixWord ++ tailWord_3845378) baseStart_3845378 baseEnd_3845378 := by
    simpa [prefixWord, tailWord_3845378, baseEnd_3845378] using wordTrace_append hprefix tailTrace_3845378
  have hstable : (prefixWord ++ tailWord_3845378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845378).length < 2 ^ (prefixWord ++ tailWord_3845378).sum := by decide
  have hdescent : baseEnd_3845378 < baseStart_3845378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845424 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 4, 2, 2]
def baseStart_3845424 : Nat := 118140960795 + 3845424 * 2 ^ 59
def prefixEnd_3845424 : Nat := 4983230072969 + 3 ^ 40 * 3845424 * 2
def baseEnd_3845424 : Nat := 1974550832335067994615223

theorem tailTrace_3845424 : CollatzResearch.WordTrace tailWord_3845424 prefixEnd_3845424 1974550832335067994615223 := by
  unfold tailWord_3845424
  simp only [CollatzResearch.WordTrace]
  refine ⟨70127067810346534489039663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93502757080462045985386217 70127067810346534489039663)
  ·
    refine ⟨105190601715519801733559495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70127067810346534489039663 105190601715519801733559495)
    ·
      refine ⟨157785902573279702600339243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105190601715519801733559495 157785902573279702600339243)
      ·
        refine ⟨236678853859919553900508865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157785902573279702600339243 236678853859919553900508865)
        ·
          refine ⟨177509140394939665425381649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236678853859919553900508865 177509140394939665425381649)
          ·
            refine ⟨133131855296204749069036237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177509140394939665425381649 133131855296204749069036237)
            ·
              refine ⟨49924445736076780900888589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133131855296204749069036237 49924445736076780900888589)
              ·
                refine ⟨18721667151028792837833221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49924445736076780900888589 18721667151028792837833221)
                ·
                  refine ⟨3510312590817898657093729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18721667151028792837833221 3510312590817898657093729)
                  ·
                    refine ⟨2632734443113423992820297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3510312590817898657093729 2632734443113423992820297)
                    ·
                      refine ⟨1974550832335067994615223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632734443113423992820297 1974550832335067994615223)
                      ·
                        rfl

theorem cell23_3845424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 2, 2].length) (baseStart_3845424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845424 prefixEnd_3845424 := by exact prefixLift 3845424
  have htrace : WordTrace (prefixWord ++ tailWord_3845424) baseStart_3845424 baseEnd_3845424 := by
    simpa [prefixWord, tailWord_3845424, baseEnd_3845424] using wordTrace_append hprefix tailTrace_3845424
  have hstable : (prefixWord ++ tailWord_3845424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845424).length < 2 ^ (prefixWord ++ tailWord_3845424).sum := by decide
  have hdescent : baseEnd_3845424 < baseStart_3845424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845444 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3845444 : Nat := 118140960795 + 3845444 * 2 ^ 59
def prefixEnd_3845444 : Nat := 4983230072969 + 3 ^ 40 * 3845444 * 2
def baseEnd_3845444 : Nat := 1974561101948157916365131

theorem tailTrace_3845444 : CollatzResearch.WordTrace tailWord_3845444 prefixEnd_3845444 1974561101948157916365131 := by
  unfold tailWord_3845444
  simp only [CollatzResearch.WordTrace]
  refine ⟨70127432540310306196903693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93503243387080408262538257 70127432540310306196903693)
  ·
    refine ⟨26297787202616364823838885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70127432540310306196903693 26297787202616364823838885)
    ·
      refine ⟨4930835100490568404469791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26297787202616364823838885 4930835100490568404469791)
      ·
        refine ⟨7396252650735852606704687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4930835100490568404469791 7396252650735852606704687)
        ·
          refine ⟨11094378976103778910057031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396252650735852606704687 11094378976103778910057031)
          ·
            refine ⟨16641568464155668365085547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094378976103778910057031 16641568464155668365085547)
            ·
              refine ⟨24962352696233502547628321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16641568464155668365085547 24962352696233502547628321)
              ·
                refine ⟨18721764522175126910721241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24962352696233502547628321 18721764522175126910721241)
                ·
                  refine ⟨14041323391631345183040931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18721764522175126910721241 14041323391631345183040931)
                  ·
                    refine ⟨21061985087447017774561397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14041323391631345183040931 21061985087447017774561397)
                    ·
                      refine ⟨1974561101948157916365131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21061985087447017774561397 1974561101948157916365131)
                      ·
                        rfl

theorem cell23_3845444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3845444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845444 prefixEnd_3845444 := by exact prefixLift 3845444
  have htrace : WordTrace (prefixWord ++ tailWord_3845444) baseStart_3845444 baseEnd_3845444 := by
    simpa [prefixWord, tailWord_3845444, baseEnd_3845444] using wordTrace_append hprefix tailTrace_3845444
  have hstable : (prefixWord ++ tailWord_3845444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845444).length < 2 ^ (prefixWord ++ tailWord_3845444).sum := by decide
  have hdescent : baseEnd_3845444 < baseStart_3845444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845450 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_3845450 : Nat := 118140960795 + 3845450 * 2 ^ 59
def prefixEnd_3845450 : Nat := 4983230072969 + 3 ^ 40 * 3845450 * 2
def baseEnd_3845450 : Nat := 1974564182832084892890103

theorem tailTrace_3845450 : CollatzResearch.WordTrace tailWord_3845450 prefixEnd_3845450 1974564182832084892890103 := by
  unfold tailWord_3845450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35063770979649718854631451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93503389279065916945683869 35063770979649718854631451)
  ·
    refine ⟨52595656469474578281947177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35063770979649718854631451 52595656469474578281947177)
    ·
      refine ⟨39446742352105933711460383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52595656469474578281947177 39446742352105933711460383)
      ·
        refine ⟨59170113528158900567190575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39446742352105933711460383 59170113528158900567190575)
        ·
          refine ⟨88755170292238350850785863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59170113528158900567190575 88755170292238350850785863)
          ·
            refine ⟨133132755438357526276178795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88755170292238350850785863 133132755438357526276178795)
            ·
              refine ⟨199699133157536289414268193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133132755438357526276178795 199699133157536289414268193)
              ·
                refine ⟨149774349868152217060701145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199699133157536289414268193 149774349868152217060701145)
                ·
                  refine ⟨112330762401114162795525859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149774349868152217060701145 112330762401114162795525859)
                  ·
                    refine ⟨168496143601671244193288789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112330762401114162795525859 168496143601671244193288789)
                    ·
                      refine ⟨1974564182832084892890103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 168496143601671244193288789 1974564182832084892890103)
                      ·
                        rfl

theorem cell23_3845450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_3845450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845450 prefixEnd_3845450 := by exact prefixLift 3845450
  have htrace : WordTrace (prefixWord ++ tailWord_3845450) baseStart_3845450 baseEnd_3845450 := by
    simpa [prefixWord, tailWord_3845450, baseEnd_3845450] using wordTrace_append hprefix tailTrace_3845450
  have hstable : (prefixWord ++ tailWord_3845450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845450).length < 2 ^ (prefixWord ++ tailWord_3845450).sum := by decide
  have hdescent : baseEnd_3845450 < baseStart_3845450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845474 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3845474 : Nat := 118140960795 + 3845474 * 2 ^ 59
def prefixEnd_3845474 : Nat := 4983230072969 + 3 ^ 40 * 3845474 * 2
def baseEnd_3845474 : Nat := 1974576506367792798989993

theorem tailTrace_3845474 : CollatzResearch.WordTrace tailWord_3845474 prefixEnd_3845474 1974576506367792798989993 := by
  unfold tailWord_3845474
  simp only [CollatzResearch.WordTrace]
  refine ⟨35063989817627981879349869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93503972847007951678266317 35063989817627981879349869)
  ·
    refine ⟨13148996181610493204756201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35063989817627981879349869 13148996181610493204756201)
    ·
      refine ⟨9861747136207869903567151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13148996181610493204756201 9861747136207869903567151)
      ·
        refine ⟨14792620704311804855350727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9861747136207869903567151 14792620704311804855350727)
        ·
          refine ⟨22188931056467707283026091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14792620704311804855350727 22188931056467707283026091)
          ·
            refine ⟨33283396584701560924539137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22188931056467707283026091 33283396584701560924539137)
            ·
              refine ⟨24962547438526170693404353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33283396584701560924539137 24962547438526170693404353)
              ·
                refine ⟨18721910578894628020053265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24962547438526170693404353 18721910578894628020053265)
                ·
                  refine ⟨14041432934170971015039949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18721910578894628020053265 14041432934170971015039949)
                  ·
                    refine ⟨5265537350314114130639981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14041432934170971015039949 5265537350314114130639981)
                    ·
                      refine ⟨1974576506367792798989993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5265537350314114130639981 1974576506367792798989993)
                      ·
                        rfl

theorem cell23_3845474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3845474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845474 prefixEnd_3845474 := by exact prefixLift 3845474
  have htrace : WordTrace (prefixWord ++ tailWord_3845474) baseStart_3845474 baseEnd_3845474 := by
    simpa [prefixWord, tailWord_3845474, baseEnd_3845474] using wordTrace_append hprefix tailTrace_3845474
  have hstable : (prefixWord ++ tailWord_3845474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845474).length < 2 ^ (prefixWord ++ tailWord_3845474).sum := by decide
  have hdescent : baseEnd_3845474 < baseStart_3845474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845477 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_3845477 : Nat := 118140960795 + 3845477 * 2 ^ 59
def prefixEnd_3845477 : Nat := 4983230072969 + 3 ^ 40 * 3845477 * 2
def baseEnd_3845477 : Nat := 658192682269918762417493

theorem tailTrace_3845477 : CollatzResearch.WordTrace tailWord_3845477 prefixEnd_3845477 658192682269918762417493 := by
  unfold tailWord_3845477
  simp only [CollatzResearch.WordTrace]
  refine ⟨140256068689501059029758685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93504045793000706019839123 140256068689501059029758685)
  ·
    refine ⟨52596025758562897136159507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140256068689501059029758685 52596025758562897136159507)
    ·
      refine ⟨78894038637844345704239261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52596025758562897136159507 78894038637844345704239261)
      ·
        refine ⟨29585264489191629639089723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78894038637844345704239261 29585264489191629639089723)
        ·
          refine ⟨44377896733787444458634585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29585264489191629639089723 44377896733787444458634585)
          ·
            refine ⟨33283422550340583343975939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44377896733787444458634585 33283422550340583343975939)
            ·
              refine ⟨49925133825510875015963909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33283422550340583343975939 49925133825510875015963909)
              ·
                refine ⟨9360962592283289065493233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49925133825510875015963909 9360962592283289065493233)
                ·
                  refine ⟨7020721944212466799119925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9360962592283289065493233 7020721944212466799119925)
                  ·
                    refine ⟨658192682269918762417493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7020721944212466799119925 658192682269918762417493)
                    ·
                      rfl

theorem cell23_3845477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_3845477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845477 prefixEnd_3845477 := by exact prefixLift 3845477
  have htrace : WordTrace (prefixWord ++ tailWord_3845477) baseStart_3845477 baseEnd_3845477 := by
    simpa [prefixWord, tailWord_3845477, baseEnd_3845477] using wordTrace_append hprefix tailTrace_3845477
  have hstable : (prefixWord ++ tailWord_3845477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845477).length < 2 ^ (prefixWord ++ tailWord_3845477).sum := by decide
  have hdescent : baseEnd_3845477 < baseStart_3845477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845484 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 2, 5, 2]
def baseStart_3845484 : Nat := 118140960795 + 3845484 * 2 ^ 59
def prefixEnd_3845484 : Nat := 4983230072969 + 3 ^ 40 * 3845484 * 2
def baseEnd_3845484 : Nat := 1974581641174337759864947

theorem tailTrace_3845484 : CollatzResearch.WordTrace tailWord_3845484 prefixEnd_3845484 1974581641174337759864947 := by
  unfold tailWord_3845484
  simp only [CollatzResearch.WordTrace]
  refine ⟨70128162000237849612631753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93504216000317132816842337 70128162000237849612631753)
  ·
    refine ⟨52596121500178387209473815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70128162000237849612631753 52596121500178387209473815)
    ·
      refine ⟨78894182250267580814210723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52596121500178387209473815 78894182250267580814210723)
      ·
        refine ⟨118341273375401371221316085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78894182250267580814210723 118341273375401371221316085)
        ·
          refine ⟨11094494378943878551998383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118341273375401371221316085 11094494378943878551998383)
          ·
            refine ⟨16641741568415817827997575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094494378943878551998383 16641741568415817827997575)
            ·
              refine ⟨24962612352623726741996363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16641741568415817827997575 24962612352623726741996363)
              ·
                refine ⟨37443918528935590112994545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24962612352623726741996363 37443918528935590112994545)
                ·
                  refine ⟨28082938896701692584745909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37443918528935590112994545 28082938896701692584745909)
                  ·
                    refine ⟨2632775521565783679819929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28082938896701692584745909 2632775521565783679819929)
                    ·
                      refine ⟨1974581641174337759864947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632775521565783679819929 1974581641174337759864947)
                      ·
                        rfl

theorem cell23_3845484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_3845484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845484 prefixEnd_3845484 := by exact prefixLift 3845484
  have htrace : WordTrace (prefixWord ++ tailWord_3845484) baseStart_3845484 baseEnd_3845484 := by
    simpa [prefixWord, tailWord_3845484, baseEnd_3845484] using wordTrace_append hprefix tailTrace_3845484
  have hstable : (prefixWord ++ tailWord_3845484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845484).length < 2 ^ (prefixWord ++ tailWord_3845484).sum := by decide
  have hdescent : baseEnd_3845484 < baseStart_3845484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845497 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_3845497 : Nat := 118140960795 + 3845497 * 2 ^ 59
def prefixEnd_3845497 : Nat := 4983230072969 + 3 ^ 40 * 3845497 * 2
def baseEnd_3845497 : Nat := 1974588316422846209002387

theorem tailTrace_3845497 : CollatzResearch.WordTrace tailWord_3845497 prefixEnd_3845497 1974588316422846209002387 := by
  unfold tailWord_3845497
  simp only [CollatzResearch.WordTrace]
  refine ⟨140256798149428602445486745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93504532099619068296991163 140256798149428602445486745)
  ·
    refine ⟨105192598612071451834115059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140256798149428602445486745 105192598612071451834115059)
    ·
      refine ⟨157788897918107177751172589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105192598612071451834115059 157788897918107177751172589)
      ·
        refine ⟨59170836719290191656689721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157788897918107177751172589 59170836719290191656689721)
        ·
          refine ⟨44378127539467643742517291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59170836719290191656689721 44378127539467643742517291)
          ·
            refine ⟨66567191309201465613775937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44378127539467643742517291 66567191309201465613775937)
            ·
              refine ⟨49925393481901099210331953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66567191309201465613775937 49925393481901099210331953)
              ·
                refine ⟨37444045111425824407748965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49925393481901099210331953 37444045111425824407748965)
                ·
                  refine ⟨7020758458392342076452931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37444045111425824407748965 7020758458392342076452931)
                  ·
                    refine ⟨10531137687588513114679397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7020758458392342076452931 10531137687588513114679397)
                    ·
                      refine ⟨1974588316422846209002387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10531137687588513114679397 1974588316422846209002387)
                      ·
                        rfl

theorem cell23_3845497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_3845497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845497 prefixEnd_3845497 := by exact prefixLift 3845497
  have htrace : WordTrace (prefixWord ++ tailWord_3845497) baseStart_3845497 baseEnd_3845497 := by
    simpa [prefixWord, tailWord_3845497, baseEnd_3845497] using wordTrace_append hprefix tailTrace_3845497
  have hstable : (prefixWord ++ tailWord_3845497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845497).length < 2 ^ (prefixWord ++ tailWord_3845497).sum := by decide
  have hdescent : baseEnd_3845497 < baseStart_3845497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845567 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 3, 5]
def baseStart_3845567 : Nat := 118140960795 + 3845567 * 2 ^ 59
def prefixEnd_3845567 : Nat := 4983230072969 + 3 ^ 40 * 3845567 * 2
def baseEnd_3845567 : Nat := 658208086689553645042355

theorem tailTrace_3845567 : CollatzResearch.WordTrace tailWord_3845567 prefixEnd_3845567 658208086689553645042355 := by
  unfold tailWord_3845567
  simp only [CollatzResearch.WordTrace]
  refine ⟨140259351259175004400534955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93506234172783336267023303 140259351259175004400534955)
  ·
    refine ⟨210389026888762506600802433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140259351259175004400534955 210389026888762506600802433)
    ·
      refine ⟨157791770166571879950601825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210389026888762506600802433 157791770166571879950601825)
      ·
        refine ⟨118343827624928909962951369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157791770166571879950601825 118343827624928909962951369)
        ·
          refine ⟨88757870718696682472213527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118343827624928909962951369 88757870718696682472213527)
          ·
            refine ⟨133136806078045023708320291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88757870718696682472213527 133136806078045023708320291)
            ·
              refine ⟨199705209117067535562480437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133136806078045023708320291 199705209117067535562480437)
              ·
                refine ⟨18722363354725081458982541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199705209117067535562480437 18722363354725081458982541)
                ·
                  refine ⟨7020886258021905547118453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18722363354725081458982541 7020886258021905547118453)
                  ·
                    refine ⟨658208086689553645042355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7020886258021905547118453 658208086689553645042355)
                    ·
                      rfl

theorem cell23_3845567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_3845567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845567 prefixEnd_3845567 := by exact prefixLift 3845567
  have htrace : WordTrace (prefixWord ++ tailWord_3845567) baseStart_3845567 baseEnd_3845567 := by
    simpa [prefixWord, tailWord_3845567, baseEnd_3845567] using wordTrace_append hprefix tailTrace_3845567
  have hstable : (prefixWord ++ tailWord_3845567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845567).length < 2 ^ (prefixWord ++ tailWord_3845567).sum := by decide
  have hdescent : baseEnd_3845567 < baseStart_3845567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845614 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_3845614 : Nat := 118140960795 + 3845614 * 2 ^ 59
def prefixEnd_3845614 : Nat := 4983230072969 + 3 ^ 40 * 3845614 * 2
def baseEnd_3845614 : Nat := 658216131219807417079783

theorem tailTrace_3845614 : CollatzResearch.WordTrace tailWord_3845614 prefixEnd_3845614 658216131219807417079783 := by
  unfold tailWord_3845614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17532633186250591428436987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93507376993336487618330597 17532633186250591428436987)
  ·
    refine ⟨26298949779375887142655481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17532633186250591428436987 26298949779375887142655481)
    ·
      refine ⟨19724212334531915356991611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26298949779375887142655481 19724212334531915356991611)
      ·
        refine ⟨29586318501797873035487417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19724212334531915356991611 29586318501797873035487417)
        ·
          refine ⟨22189738876348404776615563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29586318501797873035487417 22189738876348404776615563)
          ·
            refine ⟨33284608314522607164923345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22189738876348404776615563 33284608314522607164923345)
            ·
              refine ⟨24963456235891955373692509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33284608314522607164923345 24963456235891955373692509)
              ·
                refine ⟨9361296088459483265134691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24963456235891955373692509 9361296088459483265134691)
                ·
                  refine ⟨14041944132689224897702037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9361296088459483265134691 14041944132689224897702037)
                  ·
                    refine ⟨658216131219807417079783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14041944132689224897702037 658216131219807417079783)
                    ·
                      rfl

theorem cell23_3845614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_3845614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845614 prefixEnd_3845614 := by exact prefixLift 3845614
  have htrace : WordTrace (prefixWord ++ tailWord_3845614) baseStart_3845614 baseEnd_3845614 := by
    simpa [prefixWord, tailWord_3845614, baseEnd_3845614] using wordTrace_append hprefix tailTrace_3845614
  have hstable : (prefixWord ++ tailWord_3845614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845614).length < 2 ^ (prefixWord ++ tailWord_3845614).sum := by decide
  have hdescent : baseEnd_3845614 < baseStart_3845614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845618 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_3845618 : Nat := 118140960795 + 3845618 * 2 ^ 59
def prefixEnd_3845618 : Nat := 4983230072969 + 3 ^ 40 * 3845618 * 2
def baseEnd_3845618 : Nat := 658216815860680078529777

theorem tailTrace_3845618 : CollatzResearch.WordTrace tailWord_3845618 prefixEnd_3845618 658216815860680078529777 := by
  unfold tailWord_3845618
  simp only [CollatzResearch.WordTrace]
  refine ⟨35065302845497560027660377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93507474254660160073761005 35065302845497560027660377)
  ·
    refine ⟨26298977134123170020745283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35065302845497560027660377 26298977134123170020745283)
    ·
      refine ⟨39448465701184755031117925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26298977134123170020745283 39448465701184755031117925)
      ·
        refine ⟨7396587318972141568334611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39448465701184755031117925 7396587318972141568334611)
        ·
          refine ⟨11094880978458212352501917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396587318972141568334611 11094880978458212352501917)
          ·
            refine ⟨4160580366921829632188219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11094880978458212352501917 4160580366921829632188219)
            ·
              refine ⟨6240870550382744448282329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4160580366921829632188219 6240870550382744448282329)
              ·
                refine ⟨4680652912787058336211747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6240870550382744448282329 4680652912787058336211747)
                ·
                  refine ⟨7020979369180587504317621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680652912787058336211747 7020979369180587504317621)
                  ·
                    refine ⟨658216815860680078529777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7020979369180587504317621 658216815860680078529777)
                    ·
                      rfl

theorem cell23_3845618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_3845618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845618 prefixEnd_3845618 := by exact prefixLift 3845618
  have htrace : WordTrace (prefixWord ++ tailWord_3845618) baseStart_3845618 baseEnd_3845618 := by
    simpa [prefixWord, tailWord_3845618, baseEnd_3845618] using wordTrace_append hprefix tailTrace_3845618
  have hstable : (prefixWord ++ tailWord_3845618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845618).length < 2 ^ (prefixWord ++ tailWord_3845618).sum := by decide
  have hdescent : baseEnd_3845618 < baseStart_3845618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845644 : List Nat := [2, 2, 1, 2, 6, 10]
def baseStart_3845644 : Nat := 118140960795 + 3845644 * 2 ^ 59
def prefixEnd_3845644 : Nat := 4983230072969 + 3 ^ 40 * 3845644 * 2
def baseEnd_3845644 : Nat := 8126188469461140468577

theorem tailTrace_3845644 : CollatzResearch.WordTrace tailWord_3845644 prefixEnd_3845644 8126188469461140468577 := by
  unfold tailWord_3845644
  simp only [CollatzResearch.WordTrace]
  refine ⟨70131079839948023275543993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93508106453264031034058657 70131079839948023275543993)
  ·
    refine ⟨52598309879961017456657995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70131079839948023275543993 52598309879961017456657995)
    ·
      refine ⟨78897464819941526184986993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52598309879961017456657995 78897464819941526184986993)
      ·
        refine ⟨59173098614956144638740245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78897464819941526184986993 59173098614956144638740245)
        ·
          refine ⟨2773738997576069279940949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59173098614956144638740245 2773738997576069279940949)
          ·
            refine ⟨8126188469461140468577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2773738997576069279940949 8126188469461140468577)
            ·
              rfl

theorem cell23_3845644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 10].length) (baseStart_3845644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845644 prefixEnd_3845644 := by exact prefixLift 3845644
  have htrace : WordTrace (prefixWord ++ tailWord_3845644) baseStart_3845644 baseEnd_3845644 := by
    simpa [prefixWord, tailWord_3845644, baseEnd_3845644] using wordTrace_append hprefix tailTrace_3845644
  have hstable : (prefixWord ++ tailWord_3845644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845644).length < 2 ^ (prefixWord ++ tailWord_3845644).sum := by decide
  have hdescent : baseEnd_3845644 < baseStart_3845644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845674 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3845674 : Nat := 118140960795 + 3845674 * 2 ^ 59
def prefixEnd_3845674 : Nat := 4983230072969 + 3 ^ 40 * 3845674 * 2
def baseEnd_3845674 : Nat := 658226400832897338829691

theorem tailTrace_3845674 : CollatzResearch.WordTrace tailWord_3845674 prefixEnd_3845674 658226400832897338829691 := by
  unfold tailWord_3845674
  simp only [CollatzResearch.WordTrace]
  refine ⟨35065813467446840418670019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93508835913191574449786717 35065813467446840418670019)
  ·
    refine ⟨52598720201170260628005029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35065813467446840418670019 52598720201170260628005029)
    ·
      refine ⟨9862260037719423867750943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52598720201170260628005029 9862260037719423867750943)
      ·
        refine ⟨14793390056579135801626415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9862260037719423867750943 14793390056579135801626415)
        ·
          refine ⟨22190085084868703702439623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14793390056579135801626415 22190085084868703702439623)
          ·
            refine ⟨33285127627303055553659435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22190085084868703702439623 33285127627303055553659435)
            ·
              refine ⟨49927691440954583330489153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33285127627303055553659435 49927691440954583330489153)
              ·
                refine ⟨37445768580715937497866865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49927691440954583330489153 37445768580715937497866865)
                ·
                  refine ⟨28084326435536953123400149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37445768580715937497866865 28084326435536953123400149)
                  ·
                    refine ⟨658226400832897338829691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28084326435536953123400149 658226400832897338829691)
                    ·
                      rfl

theorem cell23_3845674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3845674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845674 prefixEnd_3845674 := by exact prefixLift 3845674
  have htrace : WordTrace (prefixWord ++ tailWord_3845674) baseStart_3845674 baseEnd_3845674 := by
    simpa [prefixWord, tailWord_3845674, baseEnd_3845674] using wordTrace_append hprefix tailTrace_3845674
  have hstable : (prefixWord ++ tailWord_3845674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845674).length < 2 ^ (prefixWord ++ tailWord_3845674).sum := by decide
  have hdescent : baseEnd_3845674 < baseStart_3845674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845692 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_3845692 : Nat := 118140960795 + 3845692 * 2 ^ 59
def prefixEnd_3845692 : Nat := 4983230072969 + 3 ^ 40 * 3845692 * 2
def baseEnd_3845692 : Nat := 1974688445150472946063991

theorem tailTrace_3845692 : CollatzResearch.WordTrace tailWord_3845692 prefixEnd_3845692 1974688445150472946063991 := by
  unfold tailWord_3845692
  simp only [CollatzResearch.WordTrace]
  refine ⟨70131955191861075374417665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93509273589148100499223553 70131955191861075374417665)
  ·
    refine ⟨52598966393895806530813249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70131955191861075374417665 52598966393895806530813249)
    ·
      refine ⟨39449224795421854898109937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52598966393895806530813249 39449224795421854898109937)
      ·
        refine ⟨29586918596566391173582453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39449224795421854898109937 29586918596566391173582453)
        ·
          refine ⟨2773773618428099172523355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29586918596566391173582453 2773773618428099172523355)
          ·
            refine ⟨4160660427642148758785033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773773618428099172523355 4160660427642148758785033)
            ·
              refine ⟨3120495320731611569088775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160660427642148758785033 3120495320731611569088775)
              ·
                refine ⟨4680742981097417353633163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120495320731611569088775 4680742981097417353633163)
                ·
                  refine ⟨7021114471646126030449745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680742981097417353633163 7021114471646126030449745)
                  ·
                    refine ⟨5265835853734594522837309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7021114471646126030449745 5265835853734594522837309)
                    ·
                      refine ⟨1974688445150472946063991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5265835853734594522837309 1974688445150472946063991)
                      ·
                        rfl

theorem cell23_3845692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_3845692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845692 prefixEnd_3845692 := by exact prefixLift 3845692
  have htrace : WordTrace (prefixWord ++ tailWord_3845692) baseStart_3845692 baseEnd_3845692 := by
    simpa [prefixWord, tailWord_3845692, baseEnd_3845692] using wordTrace_append hprefix tailTrace_3845692
  have hstable : (prefixWord ++ tailWord_3845692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845692).length < 2 ^ (prefixWord ++ tailWord_3845692).sum := by decide
  have hdescent : baseEnd_3845692 < baseStart_3845692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845771 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 2, 5, 2]
def baseStart_3845771 : Nat := 118140960795 + 3845771 * 2 ^ 59
def prefixEnd_3845771 : Nat := 4983230072969 + 3 ^ 40 * 3845771 * 2
def baseEnd_3845771 : Nat := 1974729010122178136976127

theorem tailTrace_3845771 : CollatzResearch.WordTrace tailWord_3845771 prefixEnd_3845771 1974729010122178136976127 := by
  unfold tailWord_3845771
  simp only [CollatzResearch.WordTrace]
  refine ⟨140266791750435947240961167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93511194500290631493974111 140266791750435947240961167)
  ·
    refine ⟨210400187625653920861441751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140266791750435947240961167 210400187625653920861441751)
    ·
      refine ⟨315600281438480881292162627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210400187625653920861441751 315600281438480881292162627)
      ·
        refine ⟨473400422157721321938243941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315600281438480881292162627 473400422157721321938243941)
        ·
          refine ⟨88762579154572747863420739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473400422157721321938243941 88762579154572747863420739)
          ·
            refine ⟨133143868731859121795131109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88762579154572747863420739 133143868731859121795131109)
            ·
              refine ⟨24964475387223585336587083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133143868731859121795131109 24964475387223585336587083)
              ·
                refine ⟨37446713080835378004880625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24964475387223585336587083 37446713080835378004880625)
                ·
                  refine ⟨28085034810626533503660469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37446713080835378004880625 28085034810626533503660469)
                  ·
                    refine ⟨2632972013496237515968169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28085034810626533503660469 2632972013496237515968169)
                    ·
                      refine ⟨1974729010122178136976127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2632972013496237515968169 1974729010122178136976127)
                      ·
                        rfl

theorem cell23_3845771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 5, 2].length) (baseStart_3845771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845771 prefixEnd_3845771 := by exact prefixLift 3845771
  have htrace : WordTrace (prefixWord ++ tailWord_3845771) baseStart_3845771 baseEnd_3845771 := by
    simpa [prefixWord, tailWord_3845771, baseEnd_3845771] using wordTrace_append hprefix tailTrace_3845771
  have hstable : (prefixWord ++ tailWord_3845771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845771).length < 2 ^ (prefixWord ++ tailWord_3845771).sum := by decide
  have hdescent : baseEnd_3845771 < baseStart_3845771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845828 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3845828 : Nat := 118140960795 + 3845828 * 2 ^ 59
def prefixEnd_3845828 : Nat := 4983230072969 + 3 ^ 40 * 3845828 * 2
def baseEnd_3845828 : Nat := 658252759506494804654455

theorem tailTrace_3845828 : CollatzResearch.WordTrace tailWord_3845828 prefixEnd_3845828 658252759506494804654455 := by
  unfold tailWord_3845828
  simp only [CollatzResearch.WordTrace]
  refine ⟨70134435355614722987893069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93512580474152963983857425 70134435355614722987893069)
  ·
    refine ⟨26300413258355521120459901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70134435355614722987893069 26300413258355521120459901)
    ·
      refine ⟨9862654971883320420172463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26300413258355521120459901 9862654971883320420172463)
      ·
        refine ⟨14793982457824980630258695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9862654971883320420172463 14793982457824980630258695)
        ·
          refine ⟨22190973686737470945388043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14793982457824980630258695 22190973686737470945388043)
          ·
            refine ⟨33286460530106206418082065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22190973686737470945388043 33286460530106206418082065)
            ·
              refine ⟨24964845397579654813561549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33286460530106206418082065 24964845397579654813561549)
              ·
                refine ⟨9361817024092370555085581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24964845397579654813561549 9361817024092370555085581)
                ·
                  refine ⟨3510681384034638958157093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9361817024092370555085581 3510681384034638958157093)
                  ·
                    refine ⟨658252759506494804654455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3510681384034638958157093 658252759506494804654455)
                    ·
                      rfl

theorem cell23_3845828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3845828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845828 prefixEnd_3845828 := by exact prefixLift 3845828
  have htrace : WordTrace (prefixWord ++ tailWord_3845828) baseStart_3845828 baseEnd_3845828 := by
    simpa [prefixWord, tailWord_3845828, baseEnd_3845828] using wordTrace_append hprefix tailTrace_3845828
  have hstable : (prefixWord ++ tailWord_3845828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845828).length < 2 ^ (prefixWord ++ tailWord_3845828).sum := by decide
  have hdescent : baseEnd_3845828 < baseStart_3845828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845841 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 6]
def baseStart_3845841 : Nat := 118140960795 + 3845841 * 2 ^ 59
def prefixEnd_3845841 : Nat := 4983230072969 + 3 ^ 40 * 3845841 * 2
def baseEnd_3845841 : Nat := 219418328196443651455645

theorem tailTrace_3845841 : CollatzResearch.WordTrace tailWord_3845841 prefixEnd_3845841 219418328196443651455645 := by
  unfold tailWord_3845841
  simp only [CollatzResearch.WordTrace]
  refine ⟨140269344860182349196009377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93512896573454899464006251 140269344860182349196009377)
  ·
    refine ⟨105202008645136761897007033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140269344860182349196009377 105202008645136761897007033)
    ·
      refine ⟨78901506483852571422755275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105202008645136761897007033 78901506483852571422755275)
      ·
        refine ⟨118352259725778857134132913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78901506483852571422755275 118352259725778857134132913)
        ·
          refine ⟨88764194794334142850599685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118352259725778857134132913 88764194794334142850599685)
          ·
            refine ⟨16643286523937651784487441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88764194794334142850599685 16643286523937651784487441)
            ·
              refine ⟨12482464892953238838365581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16643286523937651784487441 12482464892953238838365581)
              ·
                refine ⟨4680924334857464564387093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12482464892953238838365581 4680924334857464564387093)
                ·
                  refine ⟨219418328196443651455645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4680924334857464564387093 219418328196443651455645)
                  ·
                    rfl

theorem cell23_3845841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 6].length) (baseStart_3845841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845841 prefixEnd_3845841 := by exact prefixLift 3845841
  have htrace : WordTrace (prefixWord ++ tailWord_3845841) baseStart_3845841 baseEnd_3845841 := by
    simpa [prefixWord, tailWord_3845841, baseEnd_3845841] using wordTrace_append hprefix tailTrace_3845841
  have hstable : (prefixWord ++ tailWord_3845841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845841).length < 2 ^ (prefixWord ++ tailWord_3845841).sum := by decide
  have hdescent : baseEnd_3845841 < baseStart_3845841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845852 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3845852 : Nat := 118140960795 + 3845852 * 2 ^ 59
def prefixEnd_3845852 : Nat := 4983230072969 + 3 ^ 40 * 3845852 * 2
def baseEnd_3845852 : Nat := 1974770602055192320063255

theorem tailTrace_3845852 : CollatzResearch.WordTrace tailWord_3845852 prefixEnd_3845852 1974770602055192320063255 := by
  unfold tailWord_3845852
  simp only [CollatzResearch.WordTrace]
  refine ⟨70134873031571249037329905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93513164042094998716439873 70134873031571249037329905)
  ·
    refine ⟨52601154773678436777997429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70134873031571249037329905 52601154773678436777997429)
    ·
      refine ⟨4931358260032353447937259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52601154773678436777997429 4931358260032353447937259)
      ·
        refine ⟨7397037390048530171905889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931358260032353447937259 7397037390048530171905889)
        ·
          refine ⟨5547778042536397628929417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7397037390048530171905889 5547778042536397628929417)
          ·
            refine ⟨4160833531902298221697063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5547778042536397628929417 4160833531902298221697063)
            ·
              refine ⟨6241250297853447332545595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4160833531902298221697063 6241250297853447332545595)
              ·
                refine ⟨9361875446780170998818393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6241250297853447332545595 9361875446780170998818393)
                ·
                  refine ⟨7021406585085128249113795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9361875446780170998818393 7021406585085128249113795)
                  ·
                    refine ⟨10532109877627692373670693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7021406585085128249113795 10532109877627692373670693)
                    ·
                      refine ⟨1974770602055192320063255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10532109877627692373670693 1974770602055192320063255)
                      ·
                        rfl

theorem cell23_3845852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3845852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845852 prefixEnd_3845852 := by exact prefixLift 3845852
  have htrace : WordTrace (prefixWord ++ tailWord_3845852) baseStart_3845852 baseEnd_3845852 := by
    simpa [prefixWord, tailWord_3845852, baseEnd_3845852] using wordTrace_append hprefix tailTrace_3845852
  have hstable : (prefixWord ++ tailWord_3845852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845852).length < 2 ^ (prefixWord ++ tailWord_3845852).sum := by decide
  have hdescent : baseEnd_3845852 < baseStart_3845852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845891 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 4]
def baseStart_3845891 : Nat := 118140960795 + 3845891 * 2 ^ 59
def prefixEnd_3845891 : Nat := 4983230072969 + 3 ^ 40 * 3845891 * 2
def baseEnd_3845891 : Nat := 1974790627800717667475575

theorem tailTrace_3845891 : CollatzResearch.WordTrace tailWord_3845891 prefixEnd_3845891 1974790627800717667475575 := by
  unfold tailWord_3845891
  simp only [CollatzResearch.WordTrace]
  refine ⟨140271168510001207735329527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93514112340000805156886351 140271168510001207735329527)
  ·
    refine ⟨210406752765001811602994291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140271168510001207735329527 210406752765001811602994291)
    ·
      refine ⟨315610129147502717404491437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210406752765001811602994291 315610129147502717404491437)
      ·
        refine ⟨118353798430313519026684289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315610129147502717404491437 118353798430313519026684289)
        ·
          refine ⟨88765348822735139270013217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118353798430313519026684289 88765348822735139270013217)
          ·
            refine ⟨66574011617051354452509913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88765348822735139270013217 66574011617051354452509913)
            ·
              refine ⟨49930508712788515839382435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66574011617051354452509913 49930508712788515839382435)
              ·
                refine ⟨74895763069182773759073653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49930508712788515839382435 74895763069182773759073653)
                ·
                  refine ⟨7021477787735885039913155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74895763069182773759073653 7021477787735885039913155)
                  ·
                    refine ⟨10532216681603827559869733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7021477787735885039913155 10532216681603827559869733)
                    ·
                      refine ⟨1974790627800717667475575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10532216681603827559869733 1974790627800717667475575)
                      ·
                        rfl

theorem cell23_3845891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_3845891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845891 prefixEnd_3845891 := by exact prefixLift 3845891
  have htrace : WordTrace (prefixWord ++ tailWord_3845891) baseStart_3845891 baseEnd_3845891 := by
    simpa [prefixWord, tailWord_3845891, baseEnd_3845891] using wordTrace_append hprefix tailTrace_3845891
  have hstable : (prefixWord ++ tailWord_3845891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845891).length < 2 ^ (prefixWord ++ tailWord_3845891).sum := by decide
  have hdescent : baseEnd_3845891 < baseStart_3845891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845928 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3845928 : Nat := 118140960795 + 3845928 * 2 ^ 59
def prefixEnd_3845928 : Nat := 4983230072969 + 3 ^ 40 * 3845928 * 2
def baseEnd_3845928 : Nat := 1974809626584934022712905

theorem tailTrace_3845928 : CollatzResearch.WordTrace tailWord_3845928 prefixEnd_3845928 1974809626584934022712905 := by
  unfold tailWord_3845928
  simp only [CollatzResearch.WordTrace]
  refine ⟨70136259005433581527213219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93515012007244775369617625 70136259005433581527213219)
  ·
    refine ⟨105204388508150372290819829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70136259005433581527213219 105204388508150372290819829)
    ·
      refine ⟨9862911422639097402264359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105204388508150372290819829 9862911422639097402264359)
      ·
        refine ⟨14794367133958646103396539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9862911422639097402264359 14794367133958646103396539)
        ·
          refine ⟨22191550700937969155094809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14794367133958646103396539 22191550700937969155094809)
          ·
            refine ⟨16643663025703476866321107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22191550700937969155094809 16643663025703476866321107)
            ·
              refine ⟨24965494538555215299481661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16643663025703476866321107 24965494538555215299481661)
              ·
                refine ⟨9362060451958205737305623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24965494538555215299481661 9362060451958205737305623)
                ·
                  refine ⟨14043090677937308605958435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9362060451958205737305623 14043090677937308605958435)
                  ·
                    refine ⟨21064636016905962908937653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14043090677937308605958435 21064636016905962908937653)
                    ·
                      refine ⟨1974809626584934022712905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21064636016905962908937653 1974809626584934022712905)
                      ·
                        rfl

theorem cell23_3845928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3845928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845928 prefixEnd_3845928 := by exact prefixLift 3845928
  have htrace : WordTrace (prefixWord ++ tailWord_3845928) baseStart_3845928 baseEnd_3845928 := by
    simpa [prefixWord, tailWord_3845928, baseEnd_3845928] using wordTrace_append hprefix tailTrace_3845928
  have hstable : (prefixWord ++ tailWord_3845928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845928).length < 2 ^ (prefixWord ++ tailWord_3845928).sum := by decide
  have hdescent : baseEnd_3845928 < baseStart_3845928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845975 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_3845975 : Nat := 118140960795 + 3845975 * 2 ^ 59
def prefixEnd_3845975 : Nat := 4983230072969 + 3 ^ 40 * 3845975 * 2
def baseEnd_3845975 : Nat := 1974833760175695338825189

theorem tailTrace_3845975 : CollatzResearch.WordTrace tailWord_3845975 prefixEnd_3845975 1974833760175695338825189 := by
  unfold tailWord_3845975
  simp only [CollatzResearch.WordTrace]
  refine ⟨140274232241696890081387379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93516154827797926720924919 140274232241696890081387379)
  ·
    refine ⟨210411348362545335122081069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140274232241696890081387379 210411348362545335122081069)
    ·
      refine ⟨78904255635954500670780401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210411348362545335122081069 78904255635954500670780401)
      ·
        refine ⟨59178191726965875503085301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78904255635954500670780401 59178191726965875503085301)
        ·
          refine ⟨5547955474403050828414247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59178191726965875503085301 5547955474403050828414247)
          ·
            refine ⟨8321933211604576242621371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547955474403050828414247 8321933211604576242621371)
            ·
              refine ⟨12482899817406864363932057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8321933211604576242621371 12482899817406864363932057)
              ·
                refine ⟨9362174863055148272949043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12482899817406864363932057 9362174863055148272949043)
                ·
                  refine ⟨14043262294582722409423565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9362174863055148272949043 14043262294582722409423565)
                  ·
                    refine ⟨5266223360468520903533837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14043262294582722409423565 5266223360468520903533837)
                    ·
                      refine ⟨1974833760175695338825189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5266223360468520903533837 1974833760175695338825189)
                      ·
                        rfl

theorem cell23_3845975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_3845975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845975 prefixEnd_3845975 := by exact prefixLift 3845975
  have htrace : WordTrace (prefixWord ++ tailWord_3845975) baseStart_3845975 baseEnd_3845975 := by
    simpa [prefixWord, tailWord_3845975, baseEnd_3845975] using wordTrace_append hprefix tailTrace_3845975
  have hstable : (prefixWord ++ tailWord_3845975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845975).length < 2 ^ (prefixWord ++ tailWord_3845975).sum := by decide
  have hdescent : baseEnd_3845975 < baseStart_3845975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3845992 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3845992 : Nat := 118140960795 + 3845992 * 2 ^ 59
def prefixEnd_3845992 : Nat := 4983230072969 + 3 ^ 40 * 3845992 * 2
def baseEnd_3845992 : Nat := 1974842489346821772312611

theorem tailTrace_3845992 : CollatzResearch.WordTrace tailWord_3845992 prefixEnd_3845992 1974842489346821772312611 := by
  unfold tailWord_3845992
  simp only [CollatzResearch.WordTrace]
  refine ⟨70137426141317650992378115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93516568188423534656504153 70137426141317650992378115)
  ·
    refine ⟨105206139211976476488567173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70137426141317650992378115 105206139211976476488567173)
    ·
      refine ⟨19726151102245589341606345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105206139211976476488567173 19726151102245589341606345)
      ·
        refine ⟨14794613326684192006204759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19726151102245589341606345 14794613326684192006204759)
        ·
          refine ⟨22191919990026288009307139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14794613326684192006204759 22191919990026288009307139)
          ·
            refine ⟨33287879985039432013960709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22191919990026288009307139 33287879985039432013960709)
            ·
              refine ⟨6241477497194893502617633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33287879985039432013960709 6241477497194893502617633)
              ·
                refine ⟨4681108122896170126963225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6241477497194893502617633 4681108122896170126963225)
                ·
                  refine ⟨3510831092172127595222419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4681108122896170126963225 3510831092172127595222419)
                  ·
                    refine ⟨5266246638258191392833629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3510831092172127595222419 5266246638258191392833629)
                    ·
                      refine ⟨1974842489346821772312611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5266246638258191392833629 1974842489346821772312611)
                      ·
                        rfl

theorem cell23_3845992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3845992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3845992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3845992 prefixEnd_3845992 := by exact prefixLift 3845992
  have htrace : WordTrace (prefixWord ++ tailWord_3845992) baseStart_3845992 baseEnd_3845992 := by
    simpa [prefixWord, tailWord_3845992, baseEnd_3845992] using wordTrace_append hprefix tailTrace_3845992
  have hstable : (prefixWord ++ tailWord_3845992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3845992).length < 2 ^ (prefixWord ++ tailWord_3845992).sum := by decide
  have hdescent : baseEnd_3845992 < baseStart_3845992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3845992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846015 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 6, 2, 2]
def baseStart_3846015 : Nat := 118140960795 + 3846015 * 2 ^ 59
def prefixEnd_3846015 : Nat := 4983230072969 + 3 ^ 40 * 3846015 * 2
def baseEnd_3846015 : Nat := 1974854299401875182325005

theorem tailTrace_3846015 : CollatzResearch.WordTrace tailWord_3846015 prefixEnd_3846015 1974854299401875182325005 := by
  unfold tailWord_3846015
  simp only [CollatzResearch.WordTrace]
  refine ⟨140275691161551976912843499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93517127441034651275228999 140275691161551976912843499)
  ·
    refine ⟨210413536742327965369265249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140275691161551976912843499 210413536742327965369265249)
    ·
      refine ⟨157810152556745974026948937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210413536742327965369265249 157810152556745974026948937)
      ·
        refine ⟨118357614417559480520211703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157810152556745974026948937 118357614417559480520211703)
        ·
          refine ⟨177536421626339220780317555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118357614417559480520211703 177536421626339220780317555)
          ·
            refine ⟨266304632439508831170476333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177536421626339220780317555 266304632439508831170476333)
            ·
              refine ⟨99864237164815811688928625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266304632439508831170476333 99864237164815811688928625)
              ·
                refine ⟨74898177873611858766696469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99864237164815811688928625 74898177873611858766696469)
                ·
                  refine ⟨3510852087825555879688897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74898177873611858766696469 3510852087825555879688897)
                  ·
                    refine ⟨2633139065869166909766673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3510852087825555879688897 2633139065869166909766673)
                    ·
                      refine ⟨1974854299401875182325005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633139065869166909766673 1974854299401875182325005)
                      ·
                        rfl

theorem cell23_3846015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_3846015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846015 prefixEnd_3846015 := by exact prefixLift 3846015
  have htrace : WordTrace (prefixWord ++ tailWord_3846015) baseStart_3846015 baseEnd_3846015 := by
    simpa [prefixWord, tailWord_3846015, baseEnd_3846015] using wordTrace_append hprefix tailTrace_3846015
  have hstable : (prefixWord ++ tailWord_3846015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846015).length < 2 ^ (prefixWord ++ tailWord_3846015).sum := by decide
  have hdescent : baseEnd_3846015 < baseStart_3846015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846036 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_3846036 : Nat := 118140960795 + 3846036 * 2 ^ 59
def prefixEnd_3846036 : Nat := 4983230072969 + 3 ^ 40 * 3846036 * 2
def baseEnd_3846036 : Nat := 1974865082495619600162409

theorem tailTrace_3846036 : CollatzResearch.WordTrace tailWord_3846036 prefixEnd_3846036 1974865082495619600162409 := by
  unfold tailWord_3846036
  simp only [CollatzResearch.WordTrace]
  refine ⟨70138228547237948749678981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93517638062983931666238641 70138228547237948749678981)
  ·
    refine ⟨13150917852607115390564809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70138228547237948749678981 13150917852607115390564809)
    ·
      refine ⟨9863188389455336542923607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13150917852607115390564809 9863188389455336542923607)
      ·
        refine ⟨14794782584183004814385411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9863188389455336542923607 14794782584183004814385411)
        ·
          refine ⟨22192173876274507221578117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14794782584183004814385411 22192173876274507221578117)
          ·
            refine ⟨4161032601801470104045897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22192173876274507221578117 4161032601801470104045897)
            ·
              refine ⟨3120774451351102578034423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161032601801470104045897 3120774451351102578034423)
              ·
                refine ⟨4681161677026653867051635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120774451351102578034423 4681161677026653867051635)
                ·
                  refine ⟨7021742515539980800577453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681161677026653867051635 7021742515539980800577453)
                  ·
                    refine ⟨2633153443327492800216545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7021742515539980800577453 2633153443327492800216545)
                    ·
                      refine ⟨1974865082495619600162409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633153443327492800216545 1974865082495619600162409)
                      ·
                        rfl

theorem cell23_3846036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_3846036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846036 prefixEnd_3846036 := by exact prefixLift 3846036
  have htrace : WordTrace (prefixWord ++ tailWord_3846036) baseStart_3846036 baseEnd_3846036 := by
    simpa [prefixWord, tailWord_3846036, baseEnd_3846036] using wordTrace_append hprefix tailTrace_3846036
  have hstable : (prefixWord ++ tailWord_3846036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846036).length < 2 ^ (prefixWord ++ tailWord_3846036).sum := by decide
  have hdescent : baseEnd_3846036 < baseStart_3846036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846049 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3846049 : Nat := 118140960795 + 3846049 * 2 ^ 59
def prefixEnd_3846049 : Nat := 4983230072969 + 3 ^ 40 * 3846049 * 2
def baseEnd_3846049 : Nat := 1974871757744128049299849

theorem tailTrace_3846049 : CollatzResearch.WordTrace tailWord_3846049 prefixEnd_3846049 1974871757744128049299849 := by
  unfold tailWord_3846049
  simp only [CollatzResearch.WordTrace]
  refine ⟨140276931243428800719581201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93517954162285867146387467 140276931243428800719581201)
  ·
    refine ⟨105207698432571600539685901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140276931243428800719581201 105207698432571600539685901)
    ·
      refine ⟨39452886912214350202382213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105207698432571600539685901 39452886912214350202382213)
      ·
        refine ⟨7397416296040190662946665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39452886912214350202382213 7397416296040190662946665)
        ·
          refine ⟨5548062222030142997209999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7397416296040190662946665 5548062222030142997209999)
          ·
            refine ⟨8322093333045214495814999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5548062222030142997209999 8322093333045214495814999)
            ·
              refine ⟨12483139999567821743722499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322093333045214495814999 12483139999567821743722499)
              ·
                refine ⟨18724709999351732615583749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483139999567821743722499 18724709999351732615583749)
                ·
                  refine ⟨3510883124878449865421953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18724709999351732615583749 3510883124878449865421953)
                  ·
                    refine ⟨2633162343658837399066465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3510883124878449865421953 2633162343658837399066465)
                    ·
                      refine ⟨1974871757744128049299849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633162343658837399066465 1974871757744128049299849)
                      ·
                        rfl

theorem cell23_3846049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3846049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846049 prefixEnd_3846049 := by exact prefixLift 3846049
  have htrace : WordTrace (prefixWord ++ tailWord_3846049) baseStart_3846049 baseEnd_3846049 := by
    simpa [prefixWord, tailWord_3846049, baseEnd_3846049] using wordTrace_append hprefix tailTrace_3846049
  have hstable : (prefixWord ++ tailWord_3846049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846049).length < 2 ^ (prefixWord ++ tailWord_3846049).sum := by decide
  have hdescent : baseEnd_3846049 < baseStart_3846049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846055 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 7]
def baseStart_3846055 : Nat := 118140960795 + 3846055 * 2 ^ 59
def prefixEnd_3846055 : Nat := 4983230072969 + 3 ^ 40 * 3846055 * 2
def baseEnd_3846055 : Nat := 219430537625339447313869

theorem tailTrace_3846055 : CollatzResearch.WordTrace tailWord_3846055 prefixEnd_3846055 219430537625339447313869 := by
  unfold tailWord_3846055
  simp only [CollatzResearch.WordTrace]
  refine ⟨140277150081407063744299619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93518100054271375829533079 140277150081407063744299619)
  ·
    refine ⟨210415725122110595616449429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140277150081407063744299619 210415725122110595616449429)
    ·
      refine ⟨9863237115098934169521067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210415725122110595616449429 9863237115098934169521067)
      ·
        refine ⟨14794855672648401254281601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9863237115098934169521067 14794855672648401254281601)
        ·
          refine ⟨11096141754486300940711201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14794855672648401254281601 11096141754486300940711201)
          ·
            refine ⟨8322106315864725705533401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11096141754486300940711201 8322106315864725705533401)
            ·
              refine ⟨6241579736898544279150051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8322106315864725705533401 6241579736898544279150051)
              ·
                refine ⟨9362369605347816418725077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6241579736898544279150051 9362369605347816418725077)
                ·
                  refine ⟨219430537625339447313869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9362369605347816418725077 219430537625339447313869)
                  ·
                    rfl

theorem cell23_3846055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 7].length) (baseStart_3846055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846055 prefixEnd_3846055 := by exact prefixLift 3846055
  have htrace : WordTrace (prefixWord ++ tailWord_3846055) baseStart_3846055 baseEnd_3846055 := by
    simpa [prefixWord, tailWord_3846055, baseEnd_3846055] using wordTrace_append hprefix tailTrace_3846055
  have hstable : (prefixWord ++ tailWord_3846055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846055).length < 2 ^ (prefixWord ++ tailWord_3846055).sum := by decide
  have hdescent : baseEnd_3846055 < baseStart_3846055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846065 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3846065 : Nat := 118140960795 + 3846065 * 2 ^ 59
def prefixEnd_3846065 : Nat := 4983230072969 + 3 ^ 40 * 3846065 * 2
def baseEnd_3846065 : Nat := 1974879973434599986699775

theorem tailTrace_3846065 : CollatzResearch.WordTrace tailWord_3846065 prefixEnd_3846065 1974879973434599986699775 := by
  unfold tailWord_3846065
  simp only [CollatzResearch.WordTrace]
  refine ⟨140277514811370835452163649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93518343207580556968109099 140277514811370835452163649)
  ·
    refine ⟨105208136108528126589122737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140277514811370835452163649 105208136108528126589122737)
    ·
      refine ⟨78906102081396094941842053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105208136108528126589122737 78906102081396094941842053)
      ·
        refine ⟨14794894140261767801595385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78906102081396094941842053 14794894140261767801595385)
        ·
          refine ⟨11096170605196325851196539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14794894140261767801595385 11096170605196325851196539)
          ·
            refine ⟨16644255907794488776794809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11096170605196325851196539 16644255907794488776794809)
            ·
              refine ⟨12483191930845866582596107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16644255907794488776794809 12483191930845866582596107)
              ·
                refine ⟨18724787896268799873894161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483191930845866582596107 18724787896268799873894161)
                ·
                  refine ⟨14043590922201599905420621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18724787896268799873894161 14043590922201599905420621)
                  ·
                    refine ⟨5266346595825599964532733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14043590922201599905420621 5266346595825599964532733)
                    ·
                      refine ⟨1974879973434599986699775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5266346595825599964532733 1974879973434599986699775)
                      ·
                        rfl

theorem cell23_3846065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3846065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846065 prefixEnd_3846065 := by exact prefixLift 3846065
  have htrace : WordTrace (prefixWord ++ tailWord_3846065) baseStart_3846065 baseEnd_3846065 := by
    simpa [prefixWord, tailWord_3846065, baseEnd_3846065] using wordTrace_append hprefix tailTrace_3846065
  have hstable : (prefixWord ++ tailWord_3846065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846065).length < 2 ^ (prefixWord ++ tailWord_3846065).sum := by decide
  have hdescent : baseEnd_3846065 < baseStart_3846065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846195 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 4]
def baseStart_3846195 : Nat := 118140960795 + 3846195 * 2 ^ 59
def prefixEnd_3846195 : Nat := 4983230072969 + 3 ^ 40 * 3846195 * 2
def baseEnd_3846195 : Nat := 1974946725919684478074177

theorem tailTrace_3846195 : CollatzResearch.WordTrace tailWord_3846195 prefixEnd_3846195 1974946725919684478074177 := by
  unfold tailWord_3846195
  simp only [CollatzResearch.WordTrace]
  refine ⟨140282256300899867654396039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93521504200599911769597359 140282256300899867654396039)
  ·
    refine ⟨210423384451349801481594059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140282256300899867654396039 210423384451349801481594059)
    ·
      refine ⟨315635076677024702222391089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210423384451349801481594059 315635076677024702222391089)
      ·
        refine ⟨236726307507768526666793317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315635076677024702222391089 236726307507768526666793317)
        ·
          refine ⟨44386182657706598750023747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236726307507768526666793317 44386182657706598750023747)
          ·
            refine ⟨66579273986559898125035621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44386182657706598750023747 66579273986559898125035621)
            ·
              refine ⟨12483613872479980898444179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66579273986559898125035621 12483613872479980898444179)
              ·
                refine ⟨18725420808719971347666269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483613872479980898444179 18725420808719971347666269)
                ·
                  refine ⟨7022032803269989255374851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18725420808719971347666269 7022032803269989255374851)
                  ·
                    refine ⟨10533049204904983883062277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7022032803269989255374851 10533049204904983883062277)
                    ·
                      refine ⟨1974946725919684478074177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10533049204904983883062277 1974946725919684478074177)
                      ·
                        rfl

theorem cell23_3846195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_3846195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846195 prefixEnd_3846195 := by exact prefixLift 3846195
  have htrace : WordTrace (prefixWord ++ tailWord_3846195) baseStart_3846195 baseEnd_3846195 := by
    simpa [prefixWord, tailWord_3846195, baseEnd_3846195] using wordTrace_append hprefix tailTrace_3846195
  have hstable : (prefixWord ++ tailWord_3846195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846195).length < 2 ^ (prefixWord ++ tailWord_3846195).sum := by decide
  have hdescent : baseEnd_3846195 < baseStart_3846195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846205 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_3846205 : Nat := 118140960795 + 3846205 * 2 ^ 59
def prefixEnd_3846205 : Nat := 4983230072969 + 3 ^ 40 * 3846205 * 2
def baseEnd_3846205 : Nat := 658317286908743146316377

theorem tailTrace_3846205 : CollatzResearch.WordTrace tailWord_3846205 prefixEnd_3846205 658317286908743146316377 := by
  unfold tailWord_3846205
  simp only [CollatzResearch.WordTrace]
  refine ⟨140282621030863639362260069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93521747353909092908173379 140282621030863639362260069)
  ·
    refine ⟨26302991443286932380423763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140282621030863639362260069 26302991443286932380423763)
    ·
      refine ⟨39454487164930398570635645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26302991443286932380423763 39454487164930398570635645)
      ·
        refine ⟨14795432686848899463988367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39454487164930398570635645 14795432686848899463988367)
        ·
          refine ⟨22193149030273349195982551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14795432686848899463988367 22193149030273349195982551)
          ·
            refine ⟨33289723545410023793973827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22193149030273349195982551 33289723545410023793973827)
            ·
              refine ⟨49934585318115035690960741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33289723545410023793973827 49934585318115035690960741)
              ·
                refine ⟨9362734747146569192055139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49934585318115035690960741 9362734747146569192055139)
                ·
                  refine ⟨14044102120719853788082709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9362734747146569192055139 14044102120719853788082709)
                  ·
                    refine ⟨658317286908743146316377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14044102120719853788082709 658317286908743146316377)
                    ·
                      rfl

theorem cell23_3846205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_3846205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846205 prefixEnd_3846205 := by exact prefixLift 3846205
  have htrace : WordTrace (prefixWord ++ tailWord_3846205) baseStart_3846205 baseEnd_3846205 := by
    simpa [prefixWord, tailWord_3846205, baseEnd_3846205] using wordTrace_append hprefix tailTrace_3846205
  have hstable : (prefixWord ++ tailWord_3846205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846205).length < 2 ^ (prefixWord ++ tailWord_3846205).sum := by decide
  have hdescent : baseEnd_3846205 < baseStart_3846205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846209 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3846209 : Nat := 118140960795 + 3846209 * 2 ^ 59
def prefixEnd_3846209 : Nat := 4983230072969 + 3 ^ 40 * 3846209 * 2
def baseEnd_3846209 : Nat := 658317971549615807766371

theorem tailTrace_3846209 : CollatzResearch.WordTrace tailWord_3846209 prefixEnd_3846209 658317971549615807766371 := by
  unfold tailWord_3846209
  simp only [CollatzResearch.WordTrace]
  refine ⟨140282766922849148045405681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93521844615232765363603787 140282766922849148045405681)
  ·
    refine ⟨105212075192136861034054261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140282766922849148045405681 105212075192136861034054261)
    ·
      refine ⟨9863632049262830721942587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105212075192136861034054261 9863632049262830721942587)
      ·
        refine ⟨14795448073894246082913881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9863632049262830721942587 14795448073894246082913881)
        ·
          refine ⟨11096586055420684562185411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14795448073894246082913881 11096586055420684562185411)
          ·
            refine ⟨16644879083131026843278117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11096586055420684562185411 16644879083131026843278117)
            ·
              refine ⟨3120914828087067533114647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16644879083131026843278117 3120914828087067533114647)
              ·
                refine ⟨4681372242130601299671971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120914828087067533114647 4681372242130601299671971)
                ·
                  refine ⟨7022058363195901949507957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681372242130601299671971 7022058363195901949507957)
                  ·
                    refine ⟨658317971549615807766371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7022058363195901949507957 658317971549615807766371)
                    ·
                      rfl

theorem cell23_3846209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3846209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846209 prefixEnd_3846209 := by exact prefixLift 3846209
  have htrace : WordTrace (prefixWord ++ tailWord_3846209) baseStart_3846209 baseEnd_3846209 := by
    simpa [prefixWord, tailWord_3846209, baseEnd_3846209] using wordTrace_append hprefix tailTrace_3846209
  have hstable : (prefixWord ++ tailWord_3846209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846209).length < 2 ^ (prefixWord ++ tailWord_3846209).sum := by decide
  have hdescent : baseEnd_3846209 < baseStart_3846209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846215 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_3846215 : Nat := 118140960795 + 3846215 * 2 ^ 59
def prefixEnd_3846215 : Nat := 4983230072969 + 3 ^ 40 * 3846215 * 2
def baseEnd_3846215 : Nat := 1974956995532774399824085

theorem tailTrace_3846215 : CollatzResearch.WordTrace tailWord_3846215 prefixEnd_3846215 1974956995532774399824085 := by
  unfold tailWord_3846215
  simp only [CollatzResearch.WordTrace]
  refine ⟨140282985760827411070124099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93521990507218274046749399 140282985760827411070124099)
  ·
    refine ⟨210424478641241116605186149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140282985760827411070124099 210424478641241116605186149)
    ·
      refine ⟨39454589745232709363472403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210424478641241116605186149 39454589745232709363472403)
      ·
        refine ⟨59181884617849064045208605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39454589745232709363472403 59181884617849064045208605)
        ·
          refine ⟨22193206731693399016953227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59181884617849064045208605 22193206731693399016953227)
          ·
            refine ⟨33289810097540098525429841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22193206731693399016953227 33289810097540098525429841)
            ·
              refine ⟨24967357573155073894072381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33289810097540098525429841 24967357573155073894072381)
              ·
                refine ⟨9362759089933152710277143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24967357573155073894072381 9362759089933152710277143)
                ·
                  refine ⟨14044138634899729065415715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9362759089933152710277143 14044138634899729065415715)
                  ·
                    refine ⟨21066207952349593598123573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14044138634899729065415715 21066207952349593598123573)
                    ·
                      refine ⟨1974956995532774399824085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21066207952349593598123573 1974956995532774399824085)
                      ·
                        rfl

theorem cell23_3846215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_3846215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846215 prefixEnd_3846215 := by exact prefixLift 3846215
  have htrace : WordTrace (prefixWord ++ tailWord_3846215) baseStart_3846215 baseEnd_3846215 := by
    simpa [prefixWord, tailWord_3846215, baseEnd_3846215] using wordTrace_append hprefix tailTrace_3846215
  have hstable : (prefixWord ++ tailWord_3846215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846215).length < 2 ^ (prefixWord ++ tailWord_3846215).sum := by decide
  have hdescent : baseEnd_3846215 < baseStart_3846215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846222 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_3846222 : Nat := 118140960795 + 3846222 * 2 ^ 59
def prefixEnd_3846222 : Nat := 4983230072969 + 3 ^ 40 * 3846222 * 2
def baseEnd_3846222 : Nat := 658320196632451957478851

theorem tailTrace_3846222 : CollatzResearch.WordTrace tailWord_3846222 prefixEnd_3846222 658320196632451957478851 := by
  unfold tailWord_3846222
  simp only [CollatzResearch.WordTrace]
  refine ⟨17535405133975256408203615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93522160714534700843752613 17535405133975256408203615)
  ·
    refine ⟨26303107700962884612305423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17535405133975256408203615 26303107700962884612305423)
    ·
      refine ⟨39454661551444326918458135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26303107700962884612305423 39454661551444326918458135)
      ·
        refine ⟨59181992327166490377687203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39454661551444326918458135 59181992327166490377687203)
        ·
          refine ⟨88772988490749735566530805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59181992327166490377687203 88772988490749735566530805)
          ·
            refine ⟨8322467671007787709362263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88772988490749735566530805 8322467671007787709362263)
            ·
              refine ⟨12483701506511681564043395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322467671007787709362263 12483701506511681564043395)
              ·
                refine ⟨18725552259767522346065093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483701506511681564043395 18725552259767522346065093)
                ·
                  refine ⟨3511041048706410439887205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18725552259767522346065093 3511041048706410439887205)
                  ·
                    refine ⟨658320196632451957478851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511041048706410439887205 658320196632451957478851)
                    ·
                      rfl

theorem cell23_3846222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_3846222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846222 prefixEnd_3846222 := by exact prefixLift 3846222
  have htrace : WordTrace (prefixWord ++ tailWord_3846222) baseStart_3846222 baseEnd_3846222 := by
    simpa [prefixWord, tailWord_3846222, baseEnd_3846222] using wordTrace_append hprefix tailTrace_3846222
  have hstable : (prefixWord ++ tailWord_3846222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846222).length < 2 ^ (prefixWord ++ tailWord_3846222).sum := by decide
  have hdescent : baseEnd_3846222 < baseStart_3846222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846229 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_3846229 : Nat := 118140960795 + 3846229 * 2 ^ 59
def prefixEnd_3846229 : Nat := 4983230072969 + 3 ^ 40 * 3846229 * 2
def baseEnd_3846229 : Nat := 1974964184261937345049021

theorem tailTrace_3846229 : CollatzResearch.WordTrace tailWord_3846229 prefixEnd_3846229 1974964184261937345049021 := by
  unfold tailWord_3846229
  simp only [CollatzResearch.WordTrace]
  refine ⟨140283496382776691461133741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93522330921851127640755827 140283496382776691461133741)
  ·
    refine ⟨52606311143541259297925153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140283496382776691461133741 52606311143541259297925153)
    ·
      refine ⟨39454733357655944473443865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52606311143541259297925153 39454733357655944473443865)
      ·
        refine ⟨29591050018241958355082899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39454733357655944473443865 29591050018241958355082899)
        ·
          refine ⟨44386575027362937532624349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29591050018241958355082899 44386575027362937532624349)
          ·
            refine ⟨16644965635261101574734131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44386575027362937532624349 16644965635261101574734131)
            ·
              refine ⟨24967448452891652362101197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16644965635261101574734131 24967448452891652362101197)
              ·
                refine ⟨9362793169834369635787949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24967448452891652362101197 9362793169834369635787949)
                ·
                  refine ⟨3511047438687888613420481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9362793169834369635787949 3511047438687888613420481)
                  ·
                    refine ⟨2633285579015916460065361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3511047438687888613420481 2633285579015916460065361)
                    ·
                      refine ⟨1974964184261937345049021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633285579015916460065361 1974964184261937345049021)
                      ·
                        rfl

theorem cell23_3846229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_3846229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846229 prefixEnd_3846229 := by exact prefixLift 3846229
  have htrace : WordTrace (prefixWord ++ tailWord_3846229) baseStart_3846229 baseEnd_3846229 := by
    simpa [prefixWord, tailWord_3846229, baseEnd_3846229] using wordTrace_append hprefix tailTrace_3846229
  have hstable : (prefixWord ++ tailWord_3846229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846229).length < 2 ^ (prefixWord ++ tailWord_3846229).sum := by decide
  have hdescent : baseEnd_3846229 < baseStart_3846229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846252 : List Nat := [2, 2, 1, 1, 3, 5, 2, 7]
def baseStart_3846252 : Nat := 118140960795 + 3846252 * 2 ^ 59
def prefixEnd_3846252 : Nat := 4983230072969 + 3 ^ 40 * 3846252 * 2
def baseEnd_3846252 : Nat := 73147259048777435372645

theorem tailTrace_3846252 : CollatzResearch.WordTrace tailWord_3846252 prefixEnd_3846252 73147259048777435372645 := by
  unfold tailWord_3846252
  simp only [CollatzResearch.WordTrace]
  refine ⟨70142167630846683194610505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93522890174462244259480673 70142167630846683194610505)
  ·
    refine ⟨52606625723135012395957879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70142167630846683194610505 52606625723135012395957879)
    ·
      refine ⟨78909938584702518593936819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52606625723135012395957879 78909938584702518593936819)
      ·
        refine ⟨118364907877053777890905229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78909938584702518593936819 118364907877053777890905229)
        ·
          refine ⟨44386840453895166709089461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118364907877053777890905229 44386840453895166709089461)
          ·
            refine ⟨4161266292552671878977137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44386840453895166709089461 4161266292552671878977137)
            ·
              refine ⟨3120949719414503909232853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161266292552671878977137 3120949719414503909232853)
              ·
                refine ⟨73147259048777435372645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3120949719414503909232853 73147259048777435372645)
                ·
                  rfl

theorem cell23_3846252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 7].length) (baseStart_3846252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846252 prefixEnd_3846252 := by exact prefixLift 3846252
  have htrace : WordTrace (prefixWord ++ tailWord_3846252) baseStart_3846252 baseEnd_3846252 := by
    simpa [prefixWord, tailWord_3846252, baseEnd_3846252] using wordTrace_append hprefix tailTrace_3846252
  have hstable : (prefixWord ++ tailWord_3846252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846252).length < 2 ^ (prefixWord ++ tailWord_3846252).sum := by decide
  have hdescent : baseEnd_3846252 < baseStart_3846252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846263 : List Nat := [1, 1, 3, 1, 1, 7, 1, 3, 1, 2, 2]
def baseStart_3846263 : Nat := 118140960795 + 3846263 * 2 ^ 59
def prefixEnd_3846263 : Nat := 4983230072969 + 3 ^ 40 * 3846263 * 2
def baseEnd_3846263 : Nat := 1974981642604190212023865

theorem tailTrace_3846263 : CollatzResearch.WordTrace tailWord_3846263 prefixEnd_3846263 1974981642604190212023865 := by
  unfold tailWord_3846263
  simp only [CollatzResearch.WordTrace]
  refine ⟨140284736464653515267871443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93523157643102343511914295 140284736464653515267871443)
  ·
    refine ⟨210427104696980272901807165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140284736464653515267871443 210427104696980272901807165)
    ·
      refine ⟨78910164261367602338177687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210427104696980272901807165 78910164261367602338177687)
      ·
        refine ⟨118365246392051403507266531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78910164261367602338177687 118365246392051403507266531)
        ·
          refine ⟨177547869588077105260899797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118365246392051403507266531 177547869588077105260899797)
          ·
            refine ⟨4161278193470557154552339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 177547869588077105260899797 4161278193470557154552339)
            ·
              refine ⟨6241917290205835731828509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161278193470557154552339 6241917290205835731828509)
              ·
                refine ⟨2340718983827188399435691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6241917290205835731828509 2340718983827188399435691)
                ·
                  refine ⟨3511078475740782599153537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340718983827188399435691 3511078475740782599153537)
                  ·
                    refine ⟨2633308856805586949365153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3511078475740782599153537 2633308856805586949365153)
                    ·
                      refine ⟨1974981642604190212023865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633308856805586949365153 1974981642604190212023865)
                      ·
                        rfl

theorem cell23_3846263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 2, 2].length) (baseStart_3846263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846263 prefixEnd_3846263 := by exact prefixLift 3846263
  have htrace : WordTrace (prefixWord ++ tailWord_3846263) baseStart_3846263 baseEnd_3846263 := by
    simpa [prefixWord, tailWord_3846263, baseEnd_3846263] using wordTrace_append hprefix tailTrace_3846263
  have hstable : (prefixWord ++ tailWord_3846263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846263).length < 2 ^ (prefixWord ++ tailWord_3846263).sum := by decide
  have hdescent : baseEnd_3846263 < baseStart_3846263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846272 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 5, 3, 2]
def baseStart_3846272 : Nat := 118140960795 + 3846272 * 2 ^ 59
def prefixEnd_3846272 : Nat := 4983230072969 + 3 ^ 40 * 3846272 * 2
def baseEnd_3846272 : Nat := 1974986263930080676811323

theorem tailTrace_3846272 : CollatzResearch.WordTrace tailWord_3846272 prefixEnd_3846272 1974986263930080676811323 := by
  unfold tailWord_3846272
  simp only [CollatzResearch.WordTrace]
  refine ⟨70142532360810454902474535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93523376481080606536632713 70142532360810454902474535)
  ·
    refine ⟨105213798541215682353711803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70142532360810454902474535 105213798541215682353711803)
    ·
      refine ⟨157820697811823523530567705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105213798541215682353711803 157820697811823523530567705)
      ·
        refine ⟨118365523358867642647925779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157820697811823523530567705 118365523358867642647925779)
        ·
          refine ⟨177548285038301463971888669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118365523358867642647925779 177548285038301463971888669)
          ·
            refine ⟨66580606889363048989458251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177548285038301463971888669 66580606889363048989458251)
            ·
              refine ⟨99870910334044573484187377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66580606889363048989458251 99870910334044573484187377)
              ·
                refine ⟨74903182750533430113140533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99870910334044573484187377 74903182750533430113140533)
                ·
                  refine ⟨7022173382862509073106925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74903182750533430113140533 7022173382862509073106925)
                  ·
                    refine ⟨2633315018573440902415097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7022173382862509073106925 2633315018573440902415097)
                    ·
                      refine ⟨1974986263930080676811323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633315018573440902415097 1974986263930080676811323)
                      ·
                        rfl

theorem cell23_3846272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_3846272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846272 prefixEnd_3846272 := by exact prefixLift 3846272
  have htrace : WordTrace (prefixWord ++ tailWord_3846272) baseStart_3846272 baseEnd_3846272 := by
    simpa [prefixWord, tailWord_3846272, baseEnd_3846272] using wordTrace_append hprefix tailTrace_3846272
  have hstable : (prefixWord ++ tailWord_3846272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846272).length < 2 ^ (prefixWord ++ tailWord_3846272).sum := by decide
  have hdescent : baseEnd_3846272 < baseStart_3846272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846280 : List Nat := [2, 1, 3, 4, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3846280 : Nat := 118140960795 + 3846280 * 2 ^ 59
def prefixEnd_3846280 : Nat := 4983230072969 + 3 ^ 40 * 3846280 * 2
def baseEnd_3846280 : Nat := 1974990371775316645511287

theorem tailTrace_3846280 : CollatzResearch.WordTrace tailWord_3846280 prefixEnd_3846280 1974990371775316645511287 := by
  unfold tailWord_3846280
  simp only [CollatzResearch.WordTrace]
  refine ⟨70142678252795963585620147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93523571003727951447493529 70142678252795963585620147)
  ·
    refine ⟨105214017379193945378430221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70142678252795963585620147 105214017379193945378430221)
    ·
      refine ⟨39455256517197729516911333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105214017379193945378430221 39455256517197729516911333)
      ·
        refine ⟨7397860596974574284420875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39455256517197729516911333 7397860596974574284420875)
        ·
          refine ⟨11096790895461861426631313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7397860596974574284420875 11096790895461861426631313)
          ·
            refine ⟨8322593171596396069973485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11096790895461861426631313 8322593171596396069973485)
            ·
              refine ⟨3120972439348648526240057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8322593171596396069973485 3120972439348648526240057)
              ·
                refine ⟨2340729329511486394680043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120972439348648526240057 2340729329511486394680043)
                ·
                  refine ⟨3511093994267229592020065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340729329511486394680043 3511093994267229592020065)
                  ·
                    refine ⟨2633320495700422194015049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3511093994267229592020065 2633320495700422194015049)
                    ·
                      refine ⟨1974990371775316645511287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633320495700422194015049 1974990371775316645511287)
                      ·
                        rfl

theorem cell23_3846280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3846280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846280 prefixEnd_3846280 := by exact prefixLift 3846280
  have htrace : WordTrace (prefixWord ++ tailWord_3846280) baseStart_3846280 baseEnd_3846280 := by
    simpa [prefixWord, tailWord_3846280, baseEnd_3846280] using wordTrace_append hprefix tailTrace_3846280
  have hstable : (prefixWord ++ tailWord_3846280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846280).length < 2 ^ (prefixWord ++ tailWord_3846280).sum := by decide
  have hdescent : baseEnd_3846280 < baseStart_3846280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846296 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3846296 : Nat := 118140960795 + 3846296 * 2 ^ 59
def prefixEnd_3846296 : Nat := 4983230072969 + 3 ^ 40 * 3846296 * 2
def baseEnd_3846296 : Nat := 1974998587465788582911213

theorem tailTrace_3846296 : CollatzResearch.WordTrace tailWord_3846296 prefixEnd_3846296 1974998587465788582911213 := by
  unfold tailWord_3846296
  simp only [CollatzResearch.WordTrace]
  refine ⟨70142970036766980951911371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93523960049022641269215161 70142970036766980951911371)
  ·
    refine ⟨105214455055150471427867057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70142970036766980951911371 105214455055150471427867057)
    ·
      refine ⟨78910841291362853570900293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105214455055150471427867057 78910841291362853570900293)
      ·
        refine ⟨14795782742130535044543805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78910841291362853570900293 14795782742130535044543805)
        ·
          refine ⟨5548418528298950641703927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14795782742130535044543805 5548418528298950641703927)
          ·
            refine ⟨8322627792448425962555891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5548418528298950641703927 8322627792448425962555891)
            ·
              refine ⟨12483941688672638943833837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322627792448425962555891 12483941688672638943833837)
              ·
                refine ⟨4681478133252239603937689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12483941688672638943833837 4681478133252239603937689)
                ·
                  refine ⟨3511108599939179702953267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4681478133252239603937689 3511108599939179702953267)
                  ·
                    refine ⟨5266662899908769554429901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3511108599939179702953267 5266662899908769554429901)
                    ·
                      refine ⟨1974998587465788582911213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5266662899908769554429901 1974998587465788582911213)
                      ·
                        rfl

theorem cell23_3846296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3846296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846296 prefixEnd_3846296 := by exact prefixLift 3846296
  have htrace : WordTrace (prefixWord ++ tailWord_3846296) baseStart_3846296 baseEnd_3846296 := by
    simpa [prefixWord, tailWord_3846296, baseEnd_3846296] using wordTrace_append hprefix tailTrace_3846296
  have hstable : (prefixWord ++ tailWord_3846296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846296).length < 2 ^ (prefixWord ++ tailWord_3846296).sum := by decide
  have hdescent : baseEnd_3846296 < baseStart_3846296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846306 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_3846306 : Nat := 118140960795 + 3846306 * 2 ^ 59
def prefixEnd_3846306 : Nat := 4983230072969 + 3 ^ 40 * 3846306 * 2
def baseEnd_3846306 : Nat := 1975003722272333543786167

theorem tailTrace_3846306 : CollatzResearch.WordTrace tailWord_3846306 prefixEnd_3846306 1975003722272333543786167 := by
  unfold tailWord_3846306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35071576200874433402921693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93524203202331822407791181 35071576200874433402921693)
  ·
    refine ⟨13151841075327912526095635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35071576200874433402921693 13151841075327912526095635)
    ·
      refine ⟨19727761612991868789143453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13151841075327912526095635 19727761612991868789143453)
      ·
        refine ⟨7397910604871950795928795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19727761612991868789143453 7397910604871950795928795)
        ·
          refine ⟨11096865907307926193893193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7397910604871950795928795 11096865907307926193893193)
          ·
            refine ⟨8322649430480944645419895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11096865907307926193893193 8322649430480944645419895)
            ·
              refine ⟨12483974145721416968129843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322649430480944645419895 12483974145721416968129843)
              ·
                refine ⟨18725961218582125452194765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483974145721416968129843 18725961218582125452194765)
                ·
                  refine ⟨7022235456968297044573037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18725961218582125452194765 7022235456968297044573037)
                  ·
                    refine ⟨2633338296363111391714889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7022235456968297044573037 2633338296363111391714889)
                    ·
                      refine ⟨1975003722272333543786167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633338296363111391714889 1975003722272333543786167)
                      ·
                        rfl

theorem cell23_3846306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_3846306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846306 prefixEnd_3846306 := by exact prefixLift 3846306
  have htrace : WordTrace (prefixWord ++ tailWord_3846306) baseStart_3846306 baseEnd_3846306 := by
    simpa [prefixWord, tailWord_3846306, baseEnd_3846306] using wordTrace_append hprefix tailTrace_3846306
  have hstable : (prefixWord ++ tailWord_3846306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846306).length < 2 ^ (prefixWord ++ tailWord_3846306).sum := by decide
  have hdescent : baseEnd_3846306 < baseStart_3846306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846336 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 2, 2, 2]
def baseStart_3846336 : Nat := 118140960795 + 3846336 * 2 ^ 59
def prefixEnd_3846336 : Nat := 4983230072969 + 3 ^ 40 * 3846336 * 2
def baseEnd_3846336 : Nat := 1975019126691968426411029

theorem tailTrace_3846336 : CollatzResearch.WordTrace tailWord_3846336 prefixEnd_3846336 1975019126691968426411029 := by
  unfold tailWord_3846336
  simp only [CollatzResearch.WordTrace]
  refine ⟨70143699496694524367639431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93524932662259365823519241 70143699496694524367639431)
  ·
    refine ⟨105215549245041786551459147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70143699496694524367639431 105215549245041786551459147)
    ·
      refine ⟨157823323867562679827188721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105215549245041786551459147 157823323867562679827188721)
      ·
        refine ⟨118367492900672009870391541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157823323867562679827188721 118367492900672009870391541)
        ·
          refine ⟨11096952459438000925349207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118367492900672009870391541 11096952459438000925349207)
          ·
            refine ⟨16645428689157001388023811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11096952459438000925349207 16645428689157001388023811)
            ·
              refine ⟨24968143033735502082035717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16645428689157001388023811 24968143033735502082035717)
              ·
                refine ⟨4681526818825406640381697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24968143033735502082035717 4681526818825406640381697)
                ·
                  refine ⟨3511145114119054980286273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4681526818825406640381697 3511145114119054980286273)
                  ·
                    refine ⟨2633358835589291235214705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3511145114119054980286273 2633358835589291235214705)
                    ·
                      refine ⟨1975019126691968426411029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633358835589291235214705 1975019126691968426411029)
                      ·
                        rfl

theorem cell23_3846336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_3846336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846336 prefixEnd_3846336 := by exact prefixLift 3846336
  have htrace : WordTrace (prefixWord ++ tailWord_3846336) baseStart_3846336 baseEnd_3846336 := by
    simpa [prefixWord, tailWord_3846336, baseEnd_3846336] using wordTrace_append hprefix tailTrace_3846336
  have hstable : (prefixWord ++ tailWord_3846336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846336).length < 2 ^ (prefixWord ++ tailWord_3846336).sum := by decide
  have hdescent : baseEnd_3846336 < baseStart_3846336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846392 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_3846392 : Nat := 118140960795 + 3846392 * 2 ^ 59
def prefixEnd_3846392 : Nat := 4983230072969 + 3 ^ 40 * 3846392 * 2
def baseEnd_3846392 : Nat := 1975047881608620207310771

theorem tailTrace_3846392 : CollatzResearch.WordTrace tailWord_3846392 prefixEnd_3846392 1975047881608620207310771 := by
  unfold tailWord_3846392
  simp only [CollatzResearch.WordTrace]
  refine ⟨70144720740593085149658715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93526294320790780199544953 70144720740593085149658715)
  ·
    refine ⟨105217081110889627724488073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70144720740593085149658715 105217081110889627724488073)
    ·
      refine ⟨78912810833167220793366055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105217081110889627724488073 78912810833167220793366055)
      ·
        refine ⟨118369216249750831190049083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78912810833167220793366055 118369216249750831190049083)
        ·
          refine ⟨177553824374626246785073625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118369216249750831190049083 177553824374626246785073625)
          ·
            refine ⟨133165368280969685088805219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177553824374626246785073625 133165368280969685088805219)
            ·
              refine ⟨199748052421454527633207829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133165368280969685088805219 199748052421454527633207829)
              ·
                refine ⟨9363189957255680982806617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199748052421454527633207829 9363189957255680982806617)
                ·
                  refine ⟨7022392467941760737104963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9363189957255680982806617 7022392467941760737104963)
                  ·
                    refine ⟨10533588701912641105657445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7022392467941760737104963 10533588701912641105657445)
                    ·
                      refine ⟨1975047881608620207310771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10533588701912641105657445 1975047881608620207310771)
                      ·
                        rfl

theorem cell23_3846392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_3846392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846392 prefixEnd_3846392 := by exact prefixLift 3846392
  have htrace : WordTrace (prefixWord ++ tailWord_3846392) baseStart_3846392 baseEnd_3846392 := by
    simpa [prefixWord, tailWord_3846392, baseEnd_3846392] using wordTrace_append hprefix tailTrace_3846392
  have hstable : (prefixWord ++ tailWord_3846392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846392).length < 2 ^ (prefixWord ++ tailWord_3846392).sum := by decide
  have hdescent : baseEnd_3846392 < baseStart_3846392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846409 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 2, 4, 2]
def baseStart_3846409 : Nat := 118140960795 + 3846409 * 2 ^ 59
def prefixEnd_3846409 : Nat := 4983230072969 + 3 ^ 40 * 3846409 * 2
def baseEnd_3846409 : Nat := 1975056610779746640798193

theorem tailTrace_3846409 : CollatzResearch.WordTrace tailWord_3846409 prefixEnd_3846409 1975056610779746640798193 := by
  unfold tailWord_3846409
  simp only [CollatzResearch.WordTrace]
  refine ⟨140290061522124582202686281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93526707681416388135124187 140290061522124582202686281)
  ·
    refine ⟨105217546141593436652014711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140290061522124582202686281 105217546141593436652014711)
    ·
      refine ⟨157826319212390154978022067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105217546141593436652014711 157826319212390154978022067)
      ·
        refine ⟨236739478818585232467033101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157826319212390154978022067 236739478818585232467033101)
        ·
          refine ⟨88777304556969462175137413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236739478818585232467033101 88777304556969462175137413)
          ·
            refine ⟨16645744604431774157838265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88777304556969462175137413 16645744604431774157838265)
            ·
              refine ⟨12484308453323830618378699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16645744604431774157838265 12484308453323830618378699)
              ·
                refine ⟨18726462679985745927568049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12484308453323830618378699 18726462679985745927568049)
                ·
                  refine ⟨14044847009989309445676037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18726462679985745927568049 14044847009989309445676037)
                  ·
                    refine ⟨2633408814372995521064257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14044847009989309445676037 2633408814372995521064257)
                    ·
                      refine ⟨1975056610779746640798193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633408814372995521064257 1975056610779746640798193)
                      ·
                        rfl

theorem cell23_3846409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 4, 2].length) (baseStart_3846409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846409 prefixEnd_3846409 := by exact prefixLift 3846409
  have htrace : WordTrace (prefixWord ++ tailWord_3846409) baseStart_3846409 baseEnd_3846409 := by
    simpa [prefixWord, tailWord_3846409, baseEnd_3846409] using wordTrace_append hprefix tailTrace_3846409
  have hstable : (prefixWord ++ tailWord_3846409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846409).length < 2 ^ (prefixWord ++ tailWord_3846409).sum := by decide
  have hdescent : baseEnd_3846409 < baseStart_3846409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846412 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_3846412 : Nat := 118140960795 + 3846412 * 2 ^ 59
def prefixEnd_3846412 : Nat := 4983230072969 + 3 ^ 40 * 3846412 * 2
def baseEnd_3846412 : Nat := 1975058151221710129060679

theorem tailTrace_3846412 : CollatzResearch.WordTrace tailWord_3846412 prefixEnd_3846412 1975058151221710129060679 := by
  unfold tailWord_3846412
  simp only [CollatzResearch.WordTrace]
  refine ⟨70145085470556856857522745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93526780627409142476696993 70145085470556856857522745)
  ·
    refine ⟨52608814102917642643142059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70145085470556856857522745 52608814102917642643142059)
    ·
      refine ⟨78913221154376463964713089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52608814102917642643142059 78913221154376463964713089)
      ·
        refine ⟨59184915865782347973534817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78913221154376463964713089 59184915865782347973534817)
        ·
          refine ⟨44388686899336760980151113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59184915865782347973534817 44388686899336760980151113)
          ·
            refine ⟨33291515174502570735113335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44388686899336760980151113 33291515174502570735113335)
            ·
              refine ⟨49937272761753856102670003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33291515174502570735113335 49937272761753856102670003)
              ·
                refine ⟨74905909142630784154005005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49937272761753856102670003 74905909142630784154005005)
                ·
                  refine ⟨28089715928486544057751877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74905909142630784154005005 28089715928486544057751877)
                  ·
                    refine ⟨5266821736591227010828477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28089715928486544057751877 5266821736591227010828477)
                    ·
                      refine ⟨1975058151221710129060679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5266821736591227010828477 1975058151221710129060679)
                      ·
                        rfl

theorem cell23_3846412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_3846412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846412 prefixEnd_3846412 := by exact prefixLift 3846412
  have htrace : WordTrace (prefixWord ++ tailWord_3846412) baseStart_3846412 baseEnd_3846412 := by
    simpa [prefixWord, tailWord_3846412, baseEnd_3846412] using wordTrace_append hprefix tailTrace_3846412
  have hstable : (prefixWord ++ tailWord_3846412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846412).length < 2 ^ (prefixWord ++ tailWord_3846412).sum := by decide
  have hdescent : baseEnd_3846412 < baseStart_3846412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846425 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_3846425 : Nat := 118140960795 + 3846425 * 2 ^ 59
def prefixEnd_3846425 : Nat := 4983230072969 + 3 ^ 40 * 3846425 * 2
def baseEnd_3846425 : Nat := 1975064826470218578198119

theorem tailTrace_3846425 : CollatzResearch.WordTrace tailWord_3846425 prefixEnd_3846425 1975064826470218578198119 := by
  unfold tailWord_3846425
  simp only [CollatzResearch.WordTrace]
  refine ⟨140290645090066616935268729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93527096726711077956845819 140290645090066616935268729)
  ·
    refine ⟨105217983817549962701451547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140290645090066616935268729 105217983817549962701451547)
    ·
      refine ⟨157826975726324944052177321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105217983817549962701451547 157826975726324944052177321)
      ·
        refine ⟨118370231794743708039132991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157826975726324944052177321 118370231794743708039132991)
        ·
          refine ⟨177555347692115562058699487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118370231794743708039132991 177555347692115562058699487)
          ·
            refine ⟨266333021538173343088049231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177555347692115562058699487 266333021538173343088049231)
            ·
              refine ⟨399499532307260014632073847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266333021538173343088049231 399499532307260014632073847)
              ·
                refine ⟨599249298460890021948110771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399499532307260014632073847 599249298460890021948110771)
                ·
                  refine ⟨898873947691335032922166157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599249298460890021948110771 898873947691335032922166157)
                  ·
                    refine ⟨337077730384250637345812309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898873947691335032922166157 337077730384250637345812309)
                    ·
                      refine ⟨1975064826470218578198119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 337077730384250637345812309 1975064826470218578198119)
                      ·
                        rfl

theorem cell23_3846425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_3846425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846425 prefixEnd_3846425 := by exact prefixLift 3846425
  have htrace : WordTrace (prefixWord ++ tailWord_3846425) baseStart_3846425 baseEnd_3846425 := by
    simpa [prefixWord, tailWord_3846425, baseEnd_3846425] using wordTrace_append hprefix tailTrace_3846425
  have hstable : (prefixWord ++ tailWord_3846425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846425).length < 2 ^ (prefixWord ++ tailWord_3846425).sum := by decide
  have hdescent : baseEnd_3846425 < baseStart_3846425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846432 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 8]
def baseStart_3846432 : Nat := 118140960795 + 3846432 * 2 ^ 59
def prefixEnd_3846432 : Nat := 4983230072969 + 3 ^ 40 * 3846432 * 2
def baseEnd_3846432 : Nat := 219452046759422227867843

theorem tailTrace_3846432 : CollatzResearch.WordTrace tailWord_3846432 prefixEnd_3846432 219452046759422227867843 := by
  unfold tailWord_3846432
  simp only [CollatzResearch.WordTrace]
  refine ⟨70145450200520628565386775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93527266934027504753849033 70145450200520628565386775)
  ·
    refine ⟨105218175300780942848080163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70145450200520628565386775 105218175300780942848080163)
    ·
      refine ⟨157827262951171414272120245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105218175300780942848080163 157827262951171414272120245)
      ·
        refine ⟨14796305901672320088011273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157827262951171414272120245 14796305901672320088011273)
        ·
          refine ⟨11097229426254240066008455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14796305901672320088011273 11097229426254240066008455)
          ·
            refine ⟨16645844139381360099012683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11097229426254240066008455 16645844139381360099012683)
            ·
              refine ⟨24968766209072040148519025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16645844139381360099012683 24968766209072040148519025)
              ·
                refine ⟨18726574656804030111389269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24968766209072040148519025 18726574656804030111389269)
                ·
                  refine ⟨219452046759422227867843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18726574656804030111389269 219452046759422227867843)
                  ·
                    rfl

theorem cell23_3846432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 8].length) (baseStart_3846432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846432 prefixEnd_3846432 := by exact prefixLift 3846432
  have htrace : WordTrace (prefixWord ++ tailWord_3846432) baseStart_3846432 baseEnd_3846432 := by
    simpa [prefixWord, tailWord_3846432, baseEnd_3846432] using wordTrace_append hprefix tailTrace_3846432
  have hstable : (prefixWord ++ tailWord_3846432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846432).length < 2 ^ (prefixWord ++ tailWord_3846432).sum := by decide
  have hdescent : baseEnd_3846432 < baseStart_3846432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846453 : List Nat := [1, 3, 3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3846453 : Nat := 118140960795 + 3846453 * 2 ^ 59
def prefixEnd_3846453 : Nat := 4983230072969 + 3 ^ 40 * 3846453 * 2
def baseEnd_3846453 : Nat := 658359734642848156215997

theorem tailTrace_3846453 : CollatzResearch.WordTrace tailWord_3846453 prefixEnd_3846453 658359734642848156215997 := by
  unfold tailWord_3846453
  simp only [CollatzResearch.WordTrace]
  refine ⟨140291666333965177717288013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93527777555976785144858675 140291666333965177717288013)
  ·
    refine ⟨52609374875236941643983005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140291666333965177717288013 52609374875236941643983005)
    ·
      refine ⟨19728515578213853116493627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52609374875236941643983005 19728515578213853116493627)
      ·
        refine ⟨29592773367320779674740441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19728515578213853116493627 29592773367320779674740441)
        ·
          refine ⟨22194580025490584756055331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29592773367320779674740441 22194580025490584756055331)
          ·
            refine ⟨33291870038235877134082997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22194580025490584756055331 33291870038235877134082997)
            ·
              refine ⟨3121112816084613481320281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33291870038235877134082997 3121112816084613481320281)
              ·
                refine ⟨2340834612063460110990211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121112816084613481320281 2340834612063460110990211)
                ·
                  refine ⟨3511251918095190166485317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340834612063460110990211 3511251918095190166485317)
                  ·
                    refine ⟨658359734642848156215997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511251918095190166485317 658359734642848156215997)
                    ·
                      rfl

theorem cell23_3846453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3846453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846453 prefixEnd_3846453 := by exact prefixLift 3846453
  have htrace : WordTrace (prefixWord ++ tailWord_3846453) baseStart_3846453 baseEnd_3846453 := by
    simpa [prefixWord, tailWord_3846453, baseEnd_3846453] using wordTrace_append hprefix tailTrace_3846453
  have hstable : (prefixWord ++ tailWord_3846453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846453).length < 2 ^ (prefixWord ++ tailWord_3846453).sum := by decide
  have hdescent : baseEnd_3846453 < baseStart_3846453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846536 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3846536 : Nat := 118140960795 + 3846536 * 2 ^ 59
def prefixEnd_3846536 : Nat := 4983230072969 + 3 ^ 40 * 3846536 * 2
def baseEnd_3846536 : Nat := 1975121822822867643910109

theorem tailTrace_3846536 : CollatzResearch.WordTrace tailWord_3846536 prefixEnd_3846536 1975121822822867643910109 := by
  unfold tailWord_3846536
  simp only [CollatzResearch.WordTrace]
  refine ⟨70147346796332241446279731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93529795728442988595039641 70147346796332241446279731)
  ·
    refine ⟨105221020194498362169419597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70147346796332241446279731 105221020194498362169419597)
    ·
      refine ⟨39457882572936885813532349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105221020194498362169419597 39457882572936885813532349)
      ·
        refine ⟨14796705964851332180074631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39457882572936885813532349 14796705964851332180074631)
        ·
          refine ⟨22195058947276998270111947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14796705964851332180074631 22195058947276998270111947)
          ·
            refine ⟨33292588420915497405167921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22195058947276998270111947 33292588420915497405167921)
            ·
              refine ⟨24969441315686623053875941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33292588420915497405167921 24969441315686623053875941)
              ·
                refine ⟨4681770246691241822601739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24969441315686623053875941 4681770246691241822601739)
                ·
                  refine ⟨7022655370036862733902609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681770246691241822601739 7022655370036862733902609)
                  ·
                    refine ⟨5266991527527647050426957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7022655370036862733902609 5266991527527647050426957)
                    ·
                      refine ⟨1975121822822867643910109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5266991527527647050426957 1975121822822867643910109)
                      ·
                        rfl

theorem cell23_3846536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3846536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846536 prefixEnd_3846536 := by exact prefixLift 3846536
  have htrace : WordTrace (prefixWord ++ tailWord_3846536) baseStart_3846536 baseEnd_3846536 := by
    simpa [prefixWord, tailWord_3846536, baseEnd_3846536] using wordTrace_append hprefix tailTrace_3846536
  have hstable : (prefixWord ++ tailWord_3846536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846536).length < 2 ^ (prefixWord ++ tailWord_3846536).sum := by decide
  have hdescent : baseEnd_3846536 < baseStart_3846536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846539 : List Nat := [1, 1, 1, 1, 4, 5, 3, 7]
def baseStart_3846539 : Nat := 118140960795 + 3846539 * 2 ^ 59
def prefixEnd_3846539 : Nat := 4983230072969 + 3 ^ 40 * 3846539 * 2
def baseEnd_3846539 : Nat := 73152717157956708598985

theorem tailTrace_3846539 : CollatzResearch.WordTrace tailWord_3846539 prefixEnd_3846539 73152717157956708598985 := by
  unfold tailWord_3846539
  simp only [CollatzResearch.WordTrace]
  refine ⟨140294803011653614404918671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93529868674435742936612447 140294803011653614404918671)
  ·
    refine ⟨210442204517480421607378007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140294803011653614404918671 210442204517480421607378007)
    ·
      refine ⟨315663306776220632411067011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210442204517480421607378007 315663306776220632411067011)
      ·
        refine ⟨473494960164330948616600517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315663306776220632411067011 473494960164330948616600517)
        ·
          refine ⟨88780305030812052865612597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473494960164330948616600517 88780305030812052865612597)
          ·
            refine ⟨8323153596638629956151181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88780305030812052865612597 8323153596638629956151181)
            ·
              refine ⟨3121182598739486233556693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8323153596638629956151181 3121182598739486233556693)
              ·
                refine ⟨73152717157956708598985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3121182598739486233556693 73152717157956708598985)
                ·
                  rfl

theorem cell23_3846539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 7].length) (baseStart_3846539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846539 prefixEnd_3846539 := by exact prefixLift 3846539
  have htrace : WordTrace (prefixWord ++ tailWord_3846539) baseStart_3846539 baseEnd_3846539 := by
    simpa [prefixWord, tailWord_3846539, baseEnd_3846539] using wordTrace_append hprefix tailTrace_3846539
  have hstable : (prefixWord ++ tailWord_3846539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846539).length < 2 ^ (prefixWord ++ tailWord_3846539).sum := by decide
  have hdescent : baseEnd_3846539 < baseStart_3846539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846570 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3846570 : Nat := 118140960795 + 3846570 * 2 ^ 59
def prefixEnd_3846570 : Nat := 4983230072969 + 3 ^ 40 * 3846570 * 2
def baseEnd_3846570 : Nat := 1975139281165120510884953

theorem tailTrace_3846570 : CollatzResearch.WordTrace tailWord_3846570 prefixEnd_3846570 1975139281165120510884953 := by
  unfold tailWord_3846570
  simp only [CollatzResearch.WordTrace]
  refine ⟨35073983418635326674824291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93530622449694204466198109 35073983418635326674824291)
  ·
    refine ⟨52610975127952990012236437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35073983418635326674824291 52610975127952990012236437)
    ·
      refine ⟨2466139459122796406823583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52610975127952990012236437 2466139459122796406823583)
      ·
        refine ⟨3699209188684194610235375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466139459122796406823583 3699209188684194610235375)
        ·
          refine ⟨5548813783026291915353063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3699209188684194610235375 5548813783026291915353063)
          ·
            refine ⟨8323220674539437873029595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5548813783026291915353063 8323220674539437873029595)
            ·
              refine ⟨12484831011809156809544393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323220674539437873029595 12484831011809156809544393)
              ·
                refine ⟨9363623258856867607158295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12484831011809156809544393 9363623258856867607158295)
                ·
                  refine ⟨14045434888285301410737443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9363623258856867607158295 14045434888285301410737443)
                  ·
                    refine ⟨21068152332427952116106165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14045434888285301410737443 21068152332427952116106165)
                    ·
                      refine ⟨1975139281165120510884953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21068152332427952116106165 1975139281165120510884953)
                      ·
                        rfl

theorem cell23_3846570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3846570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846570 prefixEnd_3846570 := by exact prefixLift 3846570
  have htrace : WordTrace (prefixWord ++ tailWord_3846570) baseStart_3846570 baseEnd_3846570 := by
    simpa [prefixWord, tailWord_3846570, baseEnd_3846570] using wordTrace_append hprefix tailTrace_3846570
  have hstable : (prefixWord ++ tailWord_3846570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846570).length < 2 ^ (prefixWord ++ tailWord_3846570).sum := by decide
  have hdescent : baseEnd_3846570 < baseStart_3846570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846606 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_3846606 : Nat := 118140960795 + 3846606 * 2 ^ 59
def prefixEnd_3846606 : Nat := 4983230072969 + 3 ^ 40 * 3846606 * 2
def baseEnd_3846606 : Nat := 1975157766468682370034787

theorem tailTrace_3846606 : CollatzResearch.WordTrace tailWord_3846606 prefixEnd_3846606 1975157766468682370034787 := by
  unfold tailWord_3846606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17537155837801360605950959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93531497801607256565071781 17537155837801360605950959)
  ·
    refine ⟨26305733756702040908926439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17537155837801360605950959 26305733756702040908926439)
    ·
      refine ⟨39458600635053061363389659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26305733756702040908926439 39458600635053061363389659)
      ·
        refine ⟨59187900952579592045084489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39458600635053061363389659 59187900952579592045084489)
        ·
          refine ⟨44390925714434694033813367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59187900952579592045084489 44390925714434694033813367)
          ·
            refine ⟨66586388571652041050720051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44390925714434694033813367 66586388571652041050720051)
            ·
              refine ⟨99879582857478061576080077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66586388571652041050720051 99879582857478061576080077)
              ·
                refine ⟨37454843571554273091030029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99879582857478061576080077 37454843571554273091030029)
                ·
                  refine ⟨14045566339332852409136261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37454843571554273091030029 14045566339332852409136261)
                  ·
                    refine ⟨2633543688624909826713049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14045566339332852409136261 2633543688624909826713049)
                    ·
                      refine ⟨1975157766468682370034787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633543688624909826713049 1975157766468682370034787)
                      ·
                        rfl

theorem cell23_3846606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_3846606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846606 prefixEnd_3846606 := by exact prefixLift 3846606
  have htrace : WordTrace (prefixWord ++ tailWord_3846606) baseStart_3846606 baseEnd_3846606 := by
    simpa [prefixWord, tailWord_3846606, baseEnd_3846606] using wordTrace_append hprefix tailTrace_3846606
  have hstable : (prefixWord ++ tailWord_3846606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846606).length < 2 ^ (prefixWord ++ tailWord_3846606).sum := by decide
  have hdescent : baseEnd_3846606 < baseStart_3846606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846623 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 4, 2, 2]
def baseStart_3846623 : Nat := 118140960795 + 3846623 * 2 ^ 59
def prefixEnd_3846623 : Nat := 4983230072969 + 3 ^ 40 * 3846623 * 2
def baseEnd_3846623 : Nat := 1975166495639808803522209

theorem tailTrace_3846623 : CollatzResearch.WordTrace tailWord_3846623 prefixEnd_3846623 1975166495639808803522209 := by
  unfold tailWord_3846623
  simp only [CollatzResearch.WordTrace]
  refine ⟨140297866743349296750976523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93531911162232864500651015 140297866743349296750976523)
  ·
    refine ⟨210446800115023945126464785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140297866743349296750976523 210446800115023945126464785)
    ·
      refine ⟨157835100086267958844848589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210446800115023945126464785 157835100086267958844848589)
      ·
        refine ⟨59188162532350484566818221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157835100086267958844848589 59188162532350484566818221)
        ·
          refine ⟨22195560949631431712556833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59188162532350484566818221 22195560949631431712556833)
          ·
            refine ⟨16646670712223573784417625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22195560949631431712556833 16646670712223573784417625)
            ·
              refine ⟨12485003034167680338313219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16646670712223573784417625 12485003034167680338313219)
              ·
                refine ⟨18727504551251520507469829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12485003034167680338313219 18727504551251520507469829)
                ·
                  refine ⟨3511407103359660095150593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18727504551251520507469829 3511407103359660095150593)
                  ·
                    refine ⟨2633555327519745071362945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3511407103359660095150593 2633555327519745071362945)
                    ·
                      refine ⟨1975166495639808803522209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633555327519745071362945 1975166495639808803522209)
                      ·
                        rfl

theorem cell23_3846623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_3846623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846623 prefixEnd_3846623 := by exact prefixLift 3846623
  have htrace : WordTrace (prefixWord ++ tailWord_3846623) baseStart_3846623 baseEnd_3846623 := by
    simpa [prefixWord, tailWord_3846623, baseEnd_3846623] using wordTrace_append hprefix tailTrace_3846623
  have hstable : (prefixWord ++ tailWord_3846623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846623).length < 2 ^ (prefixWord ++ tailWord_3846623).sum := by decide
  have hdescent : baseEnd_3846623 < baseStart_3846623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846639 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 3]
def baseStart_3846639 : Nat := 118140960795 + 3846639 * 2 ^ 59
def prefixEnd_3846639 : Nat := 4983230072969 + 3 ^ 40 * 3846639 * 2
def baseEnd_3846639 : Nat := 1975174711330280740922135

theorem tailTrace_3846639 : CollatzResearch.WordTrace tailWord_3846639 prefixEnd_3846639 1975174711330280740922135 := by
  unfold tailWord_3846639
  simp only [CollatzResearch.WordTrace]
  refine ⟨140298450311291331483558971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93532300207527554322372647 140298450311291331483558971)
  ·
    refine ⟨210447675466936997225338457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140298450311291331483558971 210447675466936997225338457)
    ·
      refine ⟨157835756600202747919003843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210447675466936997225338457 157835756600202747919003843)
      ·
        refine ⟨236753634900304121878505765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157835756600202747919003843 236753634900304121878505765)
        ·
          refine ⟨44391306543807022852219831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236753634900304121878505765 44391306543807022852219831)
          ·
            refine ⟨66586959815710534278329747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44391306543807022852219831 66586959815710534278329747)
            ·
              refine ⟨99880439723565801417494621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66586959815710534278329747 99880439723565801417494621)
              ·
                refine ⟨37455164896337175531560483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99880439723565801417494621 37455164896337175531560483)
                ·
                  refine ⟨56182747344505763297340725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37455164896337175531560483 56182747344505763297340725)
                  ·
                    refine ⟨5267132563547415309125693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56182747344505763297340725 5267132563547415309125693)
                    ·
                      refine ⟨1975174711330280740922135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5267132563547415309125693 1975174711330280740922135)
                      ·
                        rfl

theorem cell23_3846639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_3846639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846639 prefixEnd_3846639 := by exact prefixLift 3846639
  have htrace : WordTrace (prefixWord ++ tailWord_3846639) baseStart_3846639 baseEnd_3846639 := by
    simpa [prefixWord, tailWord_3846639, baseEnd_3846639] using wordTrace_append hprefix tailTrace_3846639
  have hstable : (prefixWord ++ tailWord_3846639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846639).length < 2 ^ (prefixWord ++ tailWord_3846639).sum := by decide
  have hdescent : baseEnd_3846639 < baseStart_3846639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846680 : List Nat := [2, 1, 2, 3, 3, 3, 2, 2, 5]
def baseStart_3846680 : Nat := 118140960795 + 3846680 * 2 ^ 59
def prefixEnd_3846680 : Nat := 4983230072969 + 3 ^ 40 * 3846680 * 2
def baseEnd_3846680 : Nat := 219466196004123897834383

theorem tailTrace_3846680 : CollatzResearch.WordTrace tailWord_3846680 prefixEnd_3846680 219466196004123897834383 := by
  unfold tailWord_3846680
  simp only [CollatzResearch.WordTrace]
  refine ⟨70149972852071397742900747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93533297136095196990534329 70149972852071397742900747)
  ·
    refine ⟨105224959278107096614351121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70149972852071397742900747 105224959278107096614351121)
    ·
      refine ⟨78918719458580322460763341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105224959278107096614351121 78918719458580322460763341)
      ·
        refine ⟨29594519796967620922786253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78918719458580322460763341 29594519796967620922786253)
        ·
          refine ⟨11097944923862857846044845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29594519796967620922786253 11097944923862857846044845)
          ·
            refine ⟨4161729346448571692266817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11097944923862857846044845 4161729346448571692266817)
            ·
              refine ⟨3121297009836428769200113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161729346448571692266817 3121297009836428769200113)
              ·
                refine ⟨2340972757377321576900085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121297009836428769200113 2340972757377321576900085)
                ·
                  refine ⟨219466196004123897834383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2340972757377321576900085 219466196004123897834383)
                  ·
                    rfl

theorem cell23_3846680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 5].length) (baseStart_3846680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846680 prefixEnd_3846680 := by exact prefixLift 3846680
  have htrace : WordTrace (prefixWord ++ tailWord_3846680) baseStart_3846680 baseEnd_3846680 := by
    simpa [prefixWord, tailWord_3846680, baseEnd_3846680] using wordTrace_append hprefix tailTrace_3846680
  have hstable : (prefixWord ++ tailWord_3846680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846680).length < 2 ^ (prefixWord ++ tailWord_3846680).sum := by decide
  have hdescent : baseEnd_3846680 < baseStart_3846680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846706 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_3846706 : Nat := 118140960795 + 3846706 * 2 ^ 59
def prefixEnd_3846706 : Nat := 4983230072969 + 3 ^ 40 * 3846706 * 2
def baseEnd_3846706 : Nat := 658403038178043992928109

theorem tailTrace_3846706 : CollatzResearch.WordTrace tailWord_3846706 prefixEnd_3846706 658403038178043992928109 := by
  unfold tailWord_3846706
  simp only [CollatzResearch.WordTrace]
  refine ⟨35075223500512150481561993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93533929334699067950831981 35075223500512150481561993)
  ·
    refine ⟨26306417625384112861171495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35075223500512150481561993 26306417625384112861171495)
    ·
      refine ⟨39459626438076169291757243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26306417625384112861171495 39459626438076169291757243)
      ·
        refine ⟨59189439657114253937635865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39459626438076169291757243 59189439657114253937635865)
        ·
          refine ⟨44392079742835690453226899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59189439657114253937635865 44392079742835690453226899)
          ·
            refine ⟨66588119614253535679840349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44392079742835690453226899 66588119614253535679840349)
            ·
              refine ⟨24970544855345075879940131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66588119614253535679840349 24970544855345075879940131)
              ·
                refine ⟨37455817283017613819910197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24970544855345075879940131 37455817283017613819910197)
                ·
                  refine ⟨3511482870282901295616581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37455817283017613819910197 3511482870282901295616581)
                  ·
                    refine ⟨658403038178043992928109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511482870282901295616581 658403038178043992928109)
                    ·
                      rfl

theorem cell23_3846706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_3846706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846706 prefixEnd_3846706 := by exact prefixLift 3846706
  have htrace : WordTrace (prefixWord ++ tailWord_3846706) baseStart_3846706 baseEnd_3846706 := by
    simpa [prefixWord, tailWord_3846706, baseEnd_3846706] using wordTrace_append hprefix tailTrace_3846706
  have hstable : (prefixWord ++ tailWord_3846706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846706).length < 2 ^ (prefixWord ++ tailWord_3846706).sum := by decide
  have hdescent : baseEnd_3846706 < baseStart_3846706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846710 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3846710 : Nat := 118140960795 + 3846710 * 2 ^ 59
def prefixEnd_3846710 : Nat := 4983230072969 + 3 ^ 40 * 3846710 * 2
def baseEnd_3846710 : Nat := 658403722818916654378103

theorem tailTrace_3846710 : CollatzResearch.WordTrace tailWord_3846710 prefixEnd_3846710 658403722818916654378103 := by
  unfold tailWord_3846710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8768814993377131913087099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93534026596022740406262389 8768814993377131913087099)
  ·
    refine ⟨13153222490065697869630649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8768814993377131913087099 13153222490065697869630649)
    ·
      refine ⟨9864916867549273402222987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13153222490065697869630649 9864916867549273402222987)
      ·
        refine ⟨14797375301323910103334481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9864916867549273402222987 14797375301323910103334481)
        ·
          refine ⟨11098031475992932577500861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14797375301323910103334481 11098031475992932577500861)
          ·
            refine ⟨4161761803497349716562823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11098031475992932577500861 4161761803497349716562823)
            ·
              refine ⟨6242642705246024574844235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161761803497349716562823 6242642705246024574844235)
              ·
                refine ⟨9363964057869036862266353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6242642705246024574844235 9363964057869036862266353)
                ·
                  refine ⟨7022973043401777646699765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9363964057869036862266353 7022973043401777646699765)
                  ·
                    refine ⟨658403722818916654378103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7022973043401777646699765 658403722818916654378103)
                    ·
                      rfl

theorem cell23_3846710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3846710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846710 prefixEnd_3846710 := by exact prefixLift 3846710
  have htrace : WordTrace (prefixWord ++ tailWord_3846710) baseStart_3846710 baseEnd_3846710 := by
    simpa [prefixWord, tailWord_3846710, baseEnd_3846710] using wordTrace_append hprefix tailTrace_3846710
  have hstable : (prefixWord ++ tailWord_3846710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846710).length < 2 ^ (prefixWord ++ tailWord_3846710).sum := by decide
  have hdescent : baseEnd_3846710 < baseStart_3846710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846719 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 8]
def baseStart_3846719 : Nat := 118140960795 + 3846719 * 2 ^ 59
def prefixEnd_3846719 : Nat := 4983230072969 + 3 ^ 40 * 3846719 * 2
def baseEnd_3846719 : Nat := 219468421086960047546863

theorem tailTrace_3846719 : CollatzResearch.WordTrace tailWord_3846719 prefixEnd_3846719 219468421086960047546863 := by
  unfold tailWord_3846719
  simp only [CollatzResearch.WordTrace]
  refine ⟨140301368151001505146471211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93534245434001003430980807 140301368151001505146471211)
  ·
    refine ⟨210452052226502257719706817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140301368151001505146471211 210452052226502257719706817)
    ·
      refine ⟨157839039169876693289780113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210452052226502257719706817 157839039169876693289780113)
      ·
        refine ⟨118379279377407519967335085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157839039169876693289780113 118379279377407519967335085)
        ·
          refine ⟨44392229766527819987750657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118379279377407519967335085 44392229766527819987750657)
          ·
            refine ⟨33294172324895864990812993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44392229766527819987750657 33294172324895864990812993)
            ·
              refine ⟨24970629243671898743109745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33294172324895864990812993 24970629243671898743109745)
              ·
                refine ⟨18727971932753924057332309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24970629243671898743109745 18727971932753924057332309)
                ·
                  refine ⟨219468421086960047546863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18727971932753924057332309 219468421086960047546863)
                  ·
                    rfl

theorem cell23_3846719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 8].length) (baseStart_3846719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846719 prefixEnd_3846719 := by exact prefixLift 3846719
  have htrace : WordTrace (prefixWord ++ tailWord_3846719) baseStart_3846719 baseEnd_3846719 := by
    simpa [prefixWord, tailWord_3846719, baseEnd_3846719] using wordTrace_append hprefix tailTrace_3846719
  have hstable : (prefixWord ++ tailWord_3846719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846719).length < 2 ^ (prefixWord ++ tailWord_3846719).sum := by decide
  have hdescent : baseEnd_3846719 < baseStart_3846719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846740 : List Nat := [2, 4, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_3846740 : Nat := 118140960795 + 3846740 * 2 ^ 59
def prefixEnd_3846740 : Nat := 4983230072969 + 3 ^ 40 * 3846740 * 2
def baseEnd_3846740 : Nat := 658408857625461615253057

theorem tailTrace_3846740 : CollatzResearch.WordTrace tailWord_3846740 prefixEnd_3846740 658408857625461615253057 := by
  unfold tailWord_3846740
  simp only [CollatzResearch.WordTrace]
  refine ⟨70151067041962712866492837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93534756055950283821990449 70151067041962712866492837)
  ·
    refine ⟨13153325070368008662467407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70151067041962712866492837 13153325070368008662467407)
    ·
      refine ⟨19729987605552012993701111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13153325070368008662467407 19729987605552012993701111)
      ·
        refine ⟨29594981408328019490551667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19729987605552012993701111 29594981408328019490551667)
        ·
          refine ⟨44392472112492029235827501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29594981408328019490551667 44392472112492029235827501)
          ·
            refine ⟨16647177042184510963435313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44392472112492029235827501 16647177042184510963435313)
            ·
              refine ⟨12485382781638383222576485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16647177042184510963435313 12485382781638383222576485)
              ·
                refine ⟨2341009271557196854233091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12485382781638383222576485 2341009271557196854233091)
                ·
                  refine ⟨3511513907335795281349637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341009271557196854233091 3511513907335795281349637)
                  ·
                    refine ⟨658408857625461615253057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511513907335795281349637 658408857625461615253057)
                    ·
                      rfl

theorem cell23_3846740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_3846740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846740 prefixEnd_3846740 := by exact prefixLift 3846740
  have htrace : WordTrace (prefixWord ++ tailWord_3846740) baseStart_3846740 baseEnd_3846740 := by
    simpa [prefixWord, tailWord_3846740, baseEnd_3846740] using wordTrace_append hprefix tailTrace_3846740
  have hstable : (prefixWord ++ tailWord_3846740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846740).length < 2 ^ (prefixWord ++ tailWord_3846740).sum := by decide
  have hdescent : baseEnd_3846740 < baseStart_3846740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846753 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 6]
def baseStart_3846753 : Nat := 118140960795 + 3846753 * 2 ^ 59
def prefixEnd_3846753 : Nat := 4983230072969 + 3 ^ 40 * 3846753 * 2
def baseEnd_3846753 : Nat := 219470360902765921655179

theorem tailTrace_3846753 : CollatzResearch.WordTrace tailWord_3846753 prefixEnd_3846753 219470360902765921655179 := by
  unfold tailWord_3846753
  simp only [CollatzResearch.WordTrace]
  refine ⟨140302608232878328953208913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93535072155252219302139275 140302608232878328953208913)
  ·
    refine ⟨105226956174658746714906685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140302608232878328953208913 105226956174658746714906685)
    ·
      refine ⟨39460108565497030018090007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105226956174658746714906685 39460108565497030018090007)
      ·
        refine ⟨59190162848245545027135011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39460108565497030018090007 59190162848245545027135011)
        ·
          refine ⟨88785244272368317540702517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59190162848245545027135011 88785244272368317540702517)
          ·
            refine ⟨8323616650534529769440861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88785244272368317540702517 8323616650534529769440861)
            ·
              refine ⟨3121356243950448663540323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8323616650534529769440861 3121356243950448663540323)
              ·
                refine ⟨4682034365925672995310485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121356243950448663540323 4682034365925672995310485)
                ·
                  refine ⟨219470360902765921655179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4682034365925672995310485 219470360902765921655179)
                  ·
                    rfl

theorem cell23_3846753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 6].length) (baseStart_3846753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846753 prefixEnd_3846753 := by exact prefixLift 3846753
  have htrace : WordTrace (prefixWord ++ tailWord_3846753) baseStart_3846753 baseEnd_3846753 := by
    simpa [prefixWord, tailWord_3846753, baseEnd_3846753] using wordTrace_append hprefix tailTrace_3846753
  have hstable : (prefixWord ++ tailWord_3846753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846753).length < 2 ^ (prefixWord ++ tailWord_3846753).sum := by decide
  have hdescent : baseEnd_3846753 < baseStart_3846753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846774 : List Nat := [5, 1, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_3846774 : Nat := 118140960795 + 3846774 * 2 ^ 59
def prefixEnd_3846774 : Nat := 4983230072969 + 3 ^ 40 * 3846774 * 2
def baseEnd_3846774 : Nat := 658414677072879237578005

theorem tailTrace_3846774 : CollatzResearch.WordTrace tailWord_3846774 prefixEnd_3846774 658414677072879237578005 := by
  unfold tailWord_3846774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8768960885362640596232711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93535582777201499693148917 8768960885362640596232711)
  ·
    refine ⟨13153441328043960894349067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8768960885362640596232711 13153441328043960894349067)
    ·
      refine ⟨19730161992065941341523601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13153441328043960894349067 19730161992065941341523601)
      ·
        refine ⟨14797621494049456006142701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19730161992065941341523601 14797621494049456006142701)
        ·
          refine ⟨5549108060268546002303513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14797621494049456006142701 5549108060268546002303513)
          ·
            refine ⟨4161831045201409501727635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5549108060268546002303513 4161831045201409501727635)
            ·
              refine ⟨6242746567802114252591453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161831045201409501727635 6242746567802114252591453)
              ·
                refine ⟨2341029962925792844721795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6242746567802114252591453 2341029962925792844721795)
                ·
                  refine ⟨3511544944388689267082693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341029962925792844721795 3511544944388689267082693)
                  ·
                    refine ⟨658414677072879237578005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3511544944388689267082693 658414677072879237578005)
                    ·
                      rfl

theorem cell23_3846774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_3846774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846774 prefixEnd_3846774 := by exact prefixLift 3846774
  have htrace : WordTrace (prefixWord ++ tailWord_3846774) baseStart_3846774 baseEnd_3846774 := by
    simpa [prefixWord, tailWord_3846774, baseEnd_3846774] using wordTrace_append hprefix tailTrace_3846774
  have hstable : (prefixWord ++ tailWord_3846774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846774).length < 2 ^ (prefixWord ++ tailWord_3846774).sum := by decide
  have hdescent : baseEnd_3846774 < baseStart_3846774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846817 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 1, 5]
def baseStart_3846817 : Nat := 118140960795 + 3846817 * 2 ^ 59
def prefixEnd_3846817 : Nat := 4983230072969 + 3 ^ 40 * 3846817 * 2
def baseEnd_3846817 : Nat := 658422036962260348165439

theorem tailTrace_3846817 : CollatzResearch.WordTrace tailWord_3846817 prefixEnd_3846817 658422036962260348165439 := by
  unfold tailWord_3846817
  simp only [CollatzResearch.WordTrace]
  refine ⟨140304942504646467883538705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93536628336430978589025803 140304942504646467883538705)
  ·
    refine ⟨105228706878484850912654029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140304942504646467883538705 105228706878484850912654029)
    ·
      refine ⟨39460765079431819092245261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105228706878484850912654029 39460765079431819092245261)
      ·
        refine ⟨14797786904786932159591973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39460765079431819092245261 14797786904786932159591973)
        ·
          refine ⟨2774585044647549779923495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14797786904786932159591973 2774585044647549779923495)
          ·
            refine ⟨4161877566971324669885243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774585044647549779923495 4161877566971324669885243)
            ·
              refine ⟨6242816350456987004827865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161877566971324669885243 6242816350456987004827865)
              ·
                refine ⟨4682112262842740253620899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6242816350456987004827865 4682112262842740253620899)
                ·
                  refine ⟨7023168394264110380431349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682112262842740253620899 7023168394264110380431349)
                  ·
                    refine ⟨658422036962260348165439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7023168394264110380431349 658422036962260348165439)
                    ·
                      rfl

theorem cell23_3846817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_3846817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846817 prefixEnd_3846817 := by exact prefixLift 3846817
  have htrace : WordTrace (prefixWord ++ tailWord_3846817) baseStart_3846817 baseEnd_3846817 := by
    simpa [prefixWord, tailWord_3846817, baseEnd_3846817] using wordTrace_append hprefix tailTrace_3846817
  have hstable : (prefixWord ++ tailWord_3846817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846817).length < 2 ^ (prefixWord ++ tailWord_3846817).sum := by decide
  have hdescent : baseEnd_3846817 < baseStart_3846817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846820 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_3846820 : Nat := 118140960795 + 3846820 * 2 ^ 59
def prefixEnd_3846820 : Nat := 4983230072969 + 3 ^ 40 * 3846820 * 2
def baseEnd_3846820 : Nat := 1975267651328744532758803

theorem tailTrace_3846820 : CollatzResearch.WordTrace tailWord_3846820 prefixEnd_3846820 1975267651328744532758803 := by
  unfold tailWord_3846820
  simp only [CollatzResearch.WordTrace]
  refine ⟨70152525961817799697948957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93536701282423732930598609 70152525961817799697948957)
  ·
    refine ⟨26307197235681674886730859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70152525961817799697948957 26307197235681674886730859)
    ·
      refine ⟨39460795853522512330096289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26307197235681674886730859 39460795853522512330096289)
      ·
        refine ⟨29595596890141884247572217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39460795853522512330096289 29595596890141884247572217)
        ·
          refine ⟨22196697667606413185679163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29595596890141884247572217 22196697667606413185679163)
          ·
            refine ⟨33295046501409619778518745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22196697667606413185679163 33295046501409619778518745)
            ·
              refine ⟨24971284876057214833889059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33295046501409619778518745 24971284876057214833889059)
              ·
                refine ⟨37456927314085822250833589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24971284876057214833889059 37456927314085822250833589)
                ·
                  refine ⟨3511586935695545836015649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37456927314085822250833589 3511586935695545836015649)
                  ·
                    refine ⟨2633690201771659377011737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3511586935695545836015649 2633690201771659377011737)
                    ·
                      refine ⟨1975267651328744532758803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633690201771659377011737 1975267651328744532758803)
                      ·
                        rfl

theorem cell23_3846820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_3846820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846820 prefixEnd_3846820 := by exact prefixLift 3846820
  have htrace : WordTrace (prefixWord ++ tailWord_3846820) baseStart_3846820 baseEnd_3846820 := by
    simpa [prefixWord, tailWord_3846820, baseEnd_3846820] using wordTrace_append hprefix tailTrace_3846820
  have hstable : (prefixWord ++ tailWord_3846820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846820).length < 2 ^ (prefixWord ++ tailWord_3846820).sum := by decide
  have hdescent : baseEnd_3846820 < baseStart_3846820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846830 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3846830 : Nat := 118140960795 + 3846830 * 2 ^ 59
def prefixEnd_3846830 : Nat := 4983230072969 + 3 ^ 40 * 3846830 * 2
def baseEnd_3846830 : Nat := 658424262045096497877919

theorem tailTrace_3846830 : CollatzResearch.WordTrace tailWord_3846830 prefixEnd_3846830 658424262045096497877919 := by
  unfold tailWord_3846830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17538177081699921387970243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93536944435732914069174629 17538177081699921387970243)
  ·
    refine ⟨26307265622549882081955365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17538177081699921387970243 26307265622549882081955365)
    ·
      refine ⟨4932612304228102890366631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26307265622549882081955365 4932612304228102890366631)
      ·
        refine ⟨7398918456342154335549947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932612304228102890366631 7398918456342154335549947)
        ·
          refine ⟨11098377684513231503324921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7398918456342154335549947 11098377684513231503324921)
          ·
            refine ⟨8323783263384923627493691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11098377684513231503324921 8323783263384923627493691)
            ·
              refine ⟨12485674895077385441240537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323783263384923627493691 12485674895077385441240537)
              ·
                refine ⟨9364256171308039080930403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12485674895077385441240537 9364256171308039080930403)
                ·
                  refine ⟨14046384256962058621395605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9364256171308039080930403 14046384256962058621395605)
                  ·
                    refine ⟨658424262045096497877919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14046384256962058621395605 658424262045096497877919)
                    ·
                      rfl

theorem cell23_3846830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3846830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846830 prefixEnd_3846830 := by exact prefixLift 3846830
  have htrace : WordTrace (prefixWord ++ tailWord_3846830) baseStart_3846830 baseEnd_3846830 := by
    simpa [prefixWord, tailWord_3846830, baseEnd_3846830] using wordTrace_append hprefix tailTrace_3846830
  have hstable : (prefixWord ++ tailWord_3846830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846830).length < 2 ^ (prefixWord ++ tailWord_3846830).sum := by decide
  have hdescent : baseEnd_3846830 < baseStart_3846830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846837 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_3846837 : Nat := 118140960795 + 3846837 * 2 ^ 59
def prefixEnd_3846837 : Nat := 4983230072969 + 3 ^ 40 * 3846837 * 2
def baseEnd_3846837 : Nat := 1975276380499870966246225

theorem tailTrace_3846837 : CollatzResearch.WordTrace tailWord_3846837 prefixEnd_3846837 1975276380499870966246225 := by
  unfold tailWord_3846837
  simp only [CollatzResearch.WordTrace]
  refine ⟨140305671964574011299266765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93537114643049340866177843 140305671964574011299266765)
  ·
    refine ⟨52614626986715254237225037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140305671964574011299266765 52614626986715254237225037)
    ·
      refine ⟨19730485120018220338959389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52614626986715254237225037 19730485120018220338959389)
      ·
        refine ⟨7398931920006832627109771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19730485120018220338959389 7398931920006832627109771)
        ·
          refine ⟨11098397880010248940664657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7398931920006832627109771 11098397880010248940664657)
          ·
            refine ⟨8323798410007686705498493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11098397880010248940664657 8323798410007686705498493)
            ·
              refine ⟨3121424403752882514561935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8323798410007686705498493 3121424403752882514561935)
              ·
                refine ⟨4682136605629323771842903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121424403752882514561935 4682136605629323771842903)
                ·
                  refine ⟨7023204908443985657764355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682136605629323771842903 7023204908443985657764355)
                  ·
                    refine ⟨10534807362665978486646533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7023204908443985657764355 10534807362665978486646533)
                    ·
                      refine ⟨1975276380499870966246225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10534807362665978486646533 1975276380499870966246225)
                      ·
                        rfl

theorem cell23_3846837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_3846837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846837 prefixEnd_3846837 := by exact prefixLift 3846837
  have htrace : WordTrace (prefixWord ++ tailWord_3846837) baseStart_3846837 baseEnd_3846837 := by
    simpa [prefixWord, tailWord_3846837, baseEnd_3846837] using wordTrace_append hprefix tailTrace_3846837
  have hstable : (prefixWord ++ tailWord_3846837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846837).length < 2 ^ (prefixWord ++ tailWord_3846837).sum := by decide
  have hdescent : baseEnd_3846837 < baseStart_3846837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846856 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 2, 7]
def baseStart_3846856 : Nat := 118140960795 + 3846856 * 2 ^ 59
def prefixEnd_3846856 : Nat := 4983230072969 + 3 ^ 40 * 3846856 * 2
def baseEnd_3846856 : Nat := 658428712210768797302879

theorem tailTrace_3846856 : CollatzResearch.WordTrace tailWord_3846856 prefixEnd_3846856 658428712210768797302879 := by
  unfold tailWord_3846856
  simp only [CollatzResearch.WordTrace]
  refine ⟨70153182475752588772104211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93537576634336785029472281 70153182475752588772104211)
  ·
    refine ⟨105229773713628883158156317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70153182475752588772104211 105229773713628883158156317)
    ·
      refine ⟨39461165142610831184308619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105229773713628883158156317 39461165142610831184308619)
      ·
        refine ⟨59191747713916246776462929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39461165142610831184308619 59191747713916246776462929)
        ·
          refine ⟨44393810785437185082347197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59191747713916246776462929 44393810785437185082347197)
          ·
            refine ⟨16647679044538944405880199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44393810785437185082347197 16647679044538944405880199)
            ·
              refine ⟨24971518566808416608820299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16647679044538944405880199 24971518566808416608820299)
              ·
                refine ⟨37457277850212624913230449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24971518566808416608820299 37457277850212624913230449)
                ·
                  refine ⟨28092958387659468684922837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37457277850212624913230449 28092958387659468684922837)
                  ·
                    refine ⟨658428712210768797302879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28092958387659468684922837 658428712210768797302879)
                    ·
                      rfl

theorem cell23_3846856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_3846856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846856 prefixEnd_3846856 := by exact prefixLift 3846856
  have htrace : WordTrace (prefixWord ++ tailWord_3846856) baseStart_3846856 baseEnd_3846856 := by
    simpa [prefixWord, tailWord_3846856, baseEnd_3846856] using wordTrace_append hprefix tailTrace_3846856
  have hstable : (prefixWord ++ tailWord_3846856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846856).length < 2 ^ (prefixWord ++ tailWord_3846856).sum := by decide
  have hdescent : baseEnd_3846856 < baseStart_3846856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846880 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 1, 3, 2]
def baseStart_3846880 : Nat := 118140960795 + 3846880 * 2 ^ 59
def prefixEnd_3846880 : Nat := 4983230072969 + 3 ^ 40 * 3846880 * 2
def baseEnd_3846880 : Nat := 1975298460168014298008527

theorem tailTrace_3846880 : CollatzResearch.WordTrace tailWord_3846880 prefixEnd_3846880 1975298460168014298008527 := by
  unfold tailWord_3846880
  simp only [CollatzResearch.WordTrace]
  refine ⟨70153620151709114821541047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93538160202278819762054729 70153620151709114821541047)
  ·
    refine ⟨105230430227563672232311571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70153620151709114821541047 105230430227563672232311571)
    ·
      refine ⟨157845645341345508348467357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105230430227563672232311571 157845645341345508348467357)
      ·
        refine ⟨59192117003004565630675259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157845645341345508348467357 59192117003004565630675259)
        ·
          refine ⟨88788175504506848446012889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59192117003004565630675259 88788175504506848446012889)
          ·
            refine ⟨66591131628380136334509667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88788175504506848446012889 66591131628380136334509667)
            ·
              refine ⟨99886697442570204501764501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66591131628380136334509667 99886697442570204501764501)
              ·
                refine ⟨4682188942620478336020211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99886697442570204501764501 4682188942620478336020211)
                ·
                  refine ⟨7023283413930717504030317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682188942620478336020211 7023283413930717504030317)
                  ·
                    refine ⟨2633731280224019064011369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7023283413930717504030317 2633731280224019064011369)
                    ·
                      refine ⟨1975298460168014298008527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633731280224019064011369 1975298460168014298008527)
                      ·
                        rfl

theorem cell23_3846880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_3846880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846880 prefixEnd_3846880 := by exact prefixLift 3846880
  have htrace : WordTrace (prefixWord ++ tailWord_3846880) baseStart_3846880 baseEnd_3846880 := by
    simpa [prefixWord, tailWord_3846880, baseEnd_3846880] using wordTrace_append hprefix tailTrace_3846880
  have hstable : (prefixWord ++ tailWord_3846880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846880).length < 2 ^ (prefixWord ++ tailWord_3846880).sum := by decide
  have hdescent : baseEnd_3846880 < baseStart_3846880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846896 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_3846896 : Nat := 118140960795 + 3846896 * 2 ^ 59
def prefixEnd_3846896 : Nat := 4983230072969 + 3 ^ 40 * 3846896 * 2
def baseEnd_3846896 : Nat := 1975306675858486235408453

theorem tailTrace_3846896 : CollatzResearch.WordTrace tailWord_3846896 prefixEnd_3846896 1975306675858486235408453 := by
  unfold tailWord_3846896
  simp only [CollatzResearch.WordTrace]
  refine ⟨70153911935680132187832271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93538549247573509583776361 70153911935680132187832271)
  ·
    refine ⟨105230867903520198281748407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70153911935680132187832271 105230867903520198281748407)
    ·
      refine ⟨157846301855280297422622611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105230867903520198281748407 157846301855280297422622611)
      ·
        refine ⟨236769452782920446133933917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157846301855280297422622611 236769452782920446133933917)
        ·
          refine ⟨88788544793595167300225219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236769452782920446133933917 88788544793595167300225219)
          ·
            refine ⟨133182817190392750950337829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88788544793595167300225219 133182817190392750950337829)
            ·
              refine ⟨24971778223198640803188343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133182817190392750950337829 24971778223198640803188343)
              ·
                refine ⟨37457667334797961204782515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24971778223198640803188343 37457667334797961204782515)
                ·
                  refine ⟨56186501002196941807173773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37457667334797961204782515 56186501002196941807173773)
                  ·
                    refine ⟨21069937875823853177690165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56186501002196941807173773 21069937875823853177690165)
                    ·
                      refine ⟨1975306675858486235408453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21069937875823853177690165 1975306675858486235408453)
                      ·
                        rfl

theorem cell23_3846896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_3846896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846896 prefixEnd_3846896 := by exact prefixLift 3846896
  have htrace : WordTrace (prefixWord ++ tailWord_3846896) baseStart_3846896 baseEnd_3846896 := by
    simpa [prefixWord, tailWord_3846896, baseEnd_3846896] using wordTrace_append hprefix tailTrace_3846896
  have hstable : (prefixWord ++ tailWord_3846896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846896).length < 2 ^ (prefixWord ++ tailWord_3846896).sum := by decide
  have hdescent : baseEnd_3846896 < baseStart_3846896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846963 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 4, 5]
def baseStart_3846963 : Nat := 118140960795 + 3846963 * 2 ^ 59
def prefixEnd_3846963 : Nat := 4983230072969 + 3 ^ 40 * 3846963 * 2
def baseEnd_3846963 : Nat := 658447026354112491090215

theorem tailTrace_3846963 : CollatzResearch.WordTrace tailWord_3846963 prefixEnd_3846963 658447026354112491090215 := by
  unfold tailWord_3846963
  simp only [CollatzResearch.WordTrace]
  refine ⟨140310267562117534818353543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93540178374745023212235695 140310267562117534818353543)
  ·
    refine ⟨210465401343176302227530315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140310267562117534818353543 210465401343176302227530315)
    ·
      refine ⟨315698102014764453341295473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210465401343176302227530315 315698102014764453341295473)
      ·
        refine ⟨236773576511073340005971605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315698102014764453341295473 236773576511073340005971605)
        ·
          refine ⟨11098761398956562812779919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 236773576511073340005971605 11098761398956562812779919)
          ·
            refine ⟨16648142098434844219169879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11098761398956562812779919 16648142098434844219169879)
            ·
              refine ⟨24972213147652266328754819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16648142098434844219169879 24972213147652266328754819)
              ·
                refine ⟨37458319721478399493132229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24972213147652266328754819 37458319721478399493132229)
                ·
                  refine ⟨7023434947777199904962293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37458319721478399493132229 7023434947777199904962293)
                  ·
                    refine ⟨658447026354112491090215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7023434947777199904962293 658447026354112491090215)
                    ·
                      rfl

theorem cell23_3846963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 5].length) (baseStart_3846963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846963 prefixEnd_3846963 := by exact prefixLift 3846963
  have htrace : WordTrace (prefixWord ++ tailWord_3846963) baseStart_3846963 baseEnd_3846963 := by
    simpa [prefixWord, tailWord_3846963, baseEnd_3846963] using wordTrace_append hprefix tailTrace_3846963
  have hstable : (prefixWord ++ tailWord_3846963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846963).length < 2 ^ (prefixWord ++ tailWord_3846963).sum := by decide
  have hdescent : baseEnd_3846963 < baseStart_3846963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3846983 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_3846983 : Nat := 118140960795 + 3846983 * 2 ^ 59
def prefixEnd_3846983 : Nat := 4983230072969 + 3 ^ 40 * 3846983 * 2
def baseEnd_3846983 : Nat := 1975351348675427395020553

theorem tailTrace_3846983 : CollatzResearch.WordTrace tailWord_3846983 prefixEnd_3846983 1975351348675427395020553 := by
  unfold tailWord_3846983
  simp only [CollatzResearch.WordTrace]
  refine ⟨140310997022045078234081603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93540664681363385489387735 140310997022045078234081603)
  ·
    refine ⟨210466495533067617351122405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140310997022045078234081603 210466495533067617351122405)
    ·
      refine ⟨39462467912450178253335451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210466495533067617351122405 39462467912450178253335451)
      ·
        refine ⟨59193701868675267380003177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39462467912450178253335451 59193701868675267380003177)
        ·
          refine ⟨44395276401506450535002383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59193701868675267380003177 44395276401506450535002383)
          ·
            refine ⟨66592914602259675802503575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44395276401506450535002383 66592914602259675802503575)
            ·
              refine ⟨99889371903389513703755363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66592914602259675802503575 99889371903389513703755363)
              ·
                refine ⟨149834057855084270555633045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99889371903389513703755363 149834057855084270555633045)
                ·
                  refine ⟨7023471461957075182295299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149834057855084270555633045 7023471461957075182295299)
                  ·
                    refine ⟨10535207192935612773442949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7023471461957075182295299 10535207192935612773442949)
                    ·
                      refine ⟨1975351348675427395020553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10535207192935612773442949 1975351348675427395020553)
                      ·
                        rfl

theorem cell23_3846983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_3846983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3846983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3846983 prefixEnd_3846983 := by exact prefixLift 3846983
  have htrace : WordTrace (prefixWord ++ tailWord_3846983) baseStart_3846983 baseEnd_3846983 := by
    simpa [prefixWord, tailWord_3846983, baseEnd_3846983] using wordTrace_append hprefix tailTrace_3846983
  have hstable : (prefixWord ++ tailWord_3846983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3846983).length < 2 ^ (prefixWord ++ tailWord_3846983).sum := by decide
  have hdescent : baseEnd_3846983 < baseStart_3846983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3846983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847020 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_3847020 : Nat := 118140960795 + 3847020 * 2 ^ 59
def prefixEnd_3847020 : Nat := 4983230072969 + 3 ^ 40 * 3847020 * 2
def baseEnd_3847020 : Nat := 1975370347459643750257883

theorem tailTrace_3847020 : CollatzResearch.WordTrace tailWord_3847020 prefixEnd_3847020 1975370347459643750257883 := by
  unfold tailWord_3847020
  simp only [CollatzResearch.WordTrace]
  refine ⟨70156173261455516776589257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93541564348607355702119009 70156173261455516776589257)
  ·
    refine ⟨52617129946091637582441943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70156173261455516776589257 52617129946091637582441943)
    ·
      refine ⟨78925694919137456373662915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52617129946091637582441943 78925694919137456373662915)
      ·
        refine ⟨118388542378706184560494373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78925694919137456373662915 118388542378706184560494373)
        ·
          refine ⟨22197851696007409605092695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118388542378706184560494373 22197851696007409605092695)
          ·
            refine ⟨33296777544011114407639043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22197851696007409605092695 33296777544011114407639043)
            ·
              refine ⟨49945166316016671611458565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33296777544011114407639043 49945166316016671611458565)
              ·
                refine ⟨9364718684253125927148481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49945166316016671611458565 9364718684253125927148481)
                ·
                  refine ⟨7023539013189844445361361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9364718684253125927148481 7023539013189844445361361)
                  ·
                    refine ⟨5267654259892383334021021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7023539013189844445361361 5267654259892383334021021)
                    ·
                      refine ⟨1975370347459643750257883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5267654259892383334021021 1975370347459643750257883)
                      ·
                        rfl

theorem cell23_3847020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_3847020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847020 prefixEnd_3847020 := by exact prefixLift 3847020
  have htrace : WordTrace (prefixWord ++ tailWord_3847020) baseStart_3847020 baseEnd_3847020 := by
    simpa [prefixWord, tailWord_3847020, baseEnd_3847020] using wordTrace_append hprefix tailTrace_3847020
  have hstable : (prefixWord ++ tailWord_3847020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847020).length < 2 ^ (prefixWord ++ tailWord_3847020).sum := by decide
  have hdescent : baseEnd_3847020 < baseStart_3847020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847130 : List Nat := [3, 1, 1, 2, 4, 3, 9]
def baseStart_3847130 : Nat := 118140960795 + 3847130 * 2 ^ 59
def prefixEnd_3847130 : Nat := 4983230072969 + 3 ^ 40 * 3847130 * 2
def baseEnd_3847130 : Nat := 24387985559649855801017

theorem tailTrace_3847130 : CollatzResearch.WordTrace tailWord_3847130 prefixEnd_3847130 24387985559649855801017 := by
  unfold tailWord_3847130
  simp only [CollatzResearch.WordTrace]
  refine ⟨35079089638128130584920711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93544239035008348226455229 35079089638128130584920711)
  ·
    refine ⟨52618634457192195877381067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35079089638128130584920711 52618634457192195877381067)
    ·
      refine ⟨78927951685788293816071601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52618634457192195877381067 78927951685788293816071601)
      ·
        refine ⟨59195963764341220362053701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78927951685788293816071601 59195963764341220362053701)
        ·
          refine ⟨11099243205813978817885069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59195963764341220362053701 11099243205813978817885069)
          ·
            refine ⟨4162216202180242056706901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11099243205813978817885069 4162216202180242056706901)
            ·
              refine ⟨24387985559649855801017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4162216202180242056706901 24387985559649855801017)
              ·
                rfl

theorem cell23_3847130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 9].length) (baseStart_3847130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847130 prefixEnd_3847130 := by exact prefixLift 3847130
  have htrace : WordTrace (prefixWord ++ tailWord_3847130) baseStart_3847130 baseEnd_3847130 := by
    simpa [prefixWord, tailWord_3847130, baseEnd_3847130] using wordTrace_append hprefix tailTrace_3847130
  have hstable : (prefixWord ++ tailWord_3847130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847130).length < 2 ^ (prefixWord ++ tailWord_3847130).sum := by decide
  have hdescent : baseEnd_3847130 < baseStart_3847130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847140 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_3847140 : Nat := 118140960795 + 3847140 * 2 ^ 59
def prefixEnd_3847140 : Nat := 4983230072969 + 3 ^ 40 * 3847140 * 2
def baseEnd_3847140 : Nat := 1975431965138183280757331

theorem tailTrace_3847140 : CollatzResearch.WordTrace tailWord_3847140 prefixEnd_3847140 1975431965138183280757331 := by
  unfold tailWord_3847140
  simp only [CollatzResearch.WordTrace]
  refine ⟨70158361641238147023773437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93544482188317529365031249 70158361641238147023773437)
  ·
    refine ⟨26309385615464305133915039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70158361641238147023773437 26309385615464305133915039)
    ·
      refine ⟨39464078423196457700872559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26309385615464305133915039 39464078423196457700872559)
      ·
        refine ⟨59196117634794686551308839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39464078423196457700872559 59196117634794686551308839)
        ·
          refine ⟨88794176452192029826963259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59196117634794686551308839 88794176452192029826963259)
          ·
            refine ⟨133191264678288044740444889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88794176452192029826963259 133191264678288044740444889)
            ·
              refine ⟨99893448508716033555333667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133191264678288044740444889 99893448508716033555333667)
              ·
                refine ⟨149840172763074050333000501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99893448508716033555333667 149840172763074050333000501)
                ·
                  refine ⟨14047516196538192218718797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149840172763074050333000501 14047516196538192218718797)
                  ·
                    refine ⟨5267818573701822082019549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14047516196538192218718797 5267818573701822082019549)
                    ·
                      refine ⟨1975431965138183280757331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5267818573701822082019549 1975431965138183280757331)
                      ·
                        rfl

theorem cell23_3847140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_3847140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847140 prefixEnd_3847140 := by exact prefixLift 3847140
  have htrace : WordTrace (prefixWord ++ tailWord_3847140) baseStart_3847140 baseEnd_3847140 := by
    simpa [prefixWord, tailWord_3847140, baseEnd_3847140] using wordTrace_append hprefix tailTrace_3847140
  have hstable : (prefixWord ++ tailWord_3847140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847140).length < 2 ^ (prefixWord ++ tailWord_3847140).sum := by decide
  have hdescent : baseEnd_3847140 < baseStart_3847140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847163 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 8]
def baseStart_3847163 : Nat := 118140960795 + 3847163 * 2 ^ 59
def prefixEnd_3847163 : Nat := 4983230072969 + 3 ^ 40 * 3847163 * 2
def baseEnd_3847163 : Nat := 1975443775193236690769725

theorem tailTrace_3847163 : CollatzResearch.WordTrace tailWord_3847163 prefixEnd_3847163 1975443775193236690769725 := by
  unfold tailWord_3847163
  simp only [CollatzResearch.WordTrace]
  refine ⟨140317562161392968975634143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93545041440928645983756095 140317562161392968975634143)
  ·
    refine ⟨210476343242089453463451215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140317562161392968975634143 210476343242089453463451215)
    ·
      refine ⟨315714514863134180195176823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210476343242089453463451215 315714514863134180195176823)
      ·
        refine ⟨473571772294701270292765235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315714514863134180195176823 473571772294701270292765235)
        ·
          refine ⟨710357658442051905439147853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473571772294701270292765235 710357658442051905439147853)
          ·
            refine ⟨266384121915769464539680445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 710357658442051905439147853 266384121915769464539680445)
            ·
              refine ⟨99894045718413549202380167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266384121915769464539680445 99894045718413549202380167)
              ·
                refine ⟨149841068577620323803570251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99894045718413549202380167 149841068577620323803570251)
                ·
                  refine ⟨224761602866430485705355377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149841068577620323803570251 224761602866430485705355377)
                  ·
                    refine ⟨168571202149822864279016533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 224761602866430485705355377 168571202149822864279016533)
                    ·
                      refine ⟨1975443775193236690769725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 168571202149822864279016533 1975443775193236690769725)
                      ·
                        rfl

theorem cell23_3847163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_3847163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847163 prefixEnd_3847163 := by exact prefixLift 3847163
  have htrace : WordTrace (prefixWord ++ tailWord_3847163) baseStart_3847163 baseEnd_3847163 := by
    simpa [prefixWord, tailWord_3847163, baseEnd_3847163] using wordTrace_append hprefix tailTrace_3847163
  have hstable : (prefixWord ++ tailWord_3847163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847163).length < 2 ^ (prefixWord ++ tailWord_3847163).sum := by decide
  have hdescent : baseEnd_3847163 < baseStart_3847163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847191 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3847191 : Nat := 118140960795 + 3847191 * 2 ^ 59
def prefixEnd_3847191 : Nat := 4983230072969 + 3 ^ 40 * 3847191 * 2
def baseEnd_3847191 : Nat := 1975458152651562581219597

theorem tailTrace_3847191 : CollatzResearch.WordTrace tailWord_3847191 prefixEnd_3847191 1975458152651562581219597 := by
  unfold tailWord_3847191
  simp only [CollatzResearch.WordTrace]
  refine ⟨140318583405291529757653427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93545722270194353171768951 140318583405291529757653427)
  ·
    refine ⟨210477875107937294636480141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140318583405291529757653427 210477875107937294636480141)
    ·
      refine ⟨78929203165476485488680053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210477875107937294636480141 78929203165476485488680053)
      ·
        refine ⟨7399612796763420514563755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78929203165476485488680053 7399612796763420514563755)
        ·
          refine ⟨11099419195145130771845633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399612796763420514563755 11099419195145130771845633)
          ·
            refine ⟨8324564396358848078884225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11099419195145130771845633 8324564396358848078884225)
            ·
              refine ⟨6243423297269136059163169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8324564396358848078884225 6243423297269136059163169)
              ·
                refine ⟨4682567472951852044372377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6243423297269136059163169 4682567472951852044372377)
                ·
                  refine ⟨3511925604713889033279283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4682567472951852044372377 3511925604713889033279283)
                  ·
                    refine ⟨5267888407070833549918925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3511925604713889033279283 5267888407070833549918925)
                    ·
                      refine ⟨1975458152651562581219597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5267888407070833549918925 1975458152651562581219597)
                      ·
                        rfl

theorem cell23_3847191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3847191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847191 prefixEnd_3847191 := by exact prefixLift 3847191
  have htrace : WordTrace (prefixWord ++ tailWord_3847191) baseStart_3847191 baseEnd_3847191 := by
    simpa [prefixWord, tailWord_3847191, baseEnd_3847191] using wordTrace_append hprefix tailTrace_3847191
  have hstable : (prefixWord ++ tailWord_3847191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847191).length < 2 ^ (prefixWord ++ tailWord_3847191).sum := by decide
  have hdescent : baseEnd_3847191 < baseStart_3847191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847207 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3847207 : Nat := 118140960795 + 3847207 * 2 ^ 59
def prefixEnd_3847207 : Nat := 4983230072969 + 3 ^ 40 * 3847207 * 2
def baseEnd_3847207 : Nat := 658488789447344839539841

theorem tailTrace_3847207 : CollatzResearch.WordTrace tailWord_3847207 prefixEnd_3847207 658488789447344839539841 := by
  unfold tailWord_3847207
  simp only [CollatzResearch.WordTrace]
  refine ⟨140319166973233564490235875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93546111315489042993490583 140319166973233564490235875)
  ·
    refine ⟨210478750459850346735353813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140319166973233564490235875 210478750459850346735353813)
    ·
      refine ⟨4933095713902742501609855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 210478750459850346735353813 4933095713902742501609855)
      ·
        refine ⟨7399643570854113752414783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4933095713902742501609855 7399643570854113752414783)
        ·
          refine ⟨11099465356281170628622175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399643570854113752414783 11099465356281170628622175)
          ·
            refine ⟨16649198034421755942933263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11099465356281170628622175 16649198034421755942933263)
            ·
              refine ⟨24973797051632633914399895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16649198034421755942933263 24973797051632633914399895)
              ·
                refine ⟨37460695577448950871599843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24973797051632633914399895 37460695577448950871599843)
                ·
                  refine ⟨56191043366173426307399765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37460695577448950871599843 56191043366173426307399765)
                  ·
                    refine ⟨658488789447344839539841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56191043366173426307399765 658488789447344839539841)
                    ·
                      rfl

theorem cell23_3847207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3847207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847207 prefixEnd_3847207 := by exact prefixLift 3847207
  have htrace : WordTrace (prefixWord ++ tailWord_3847207) baseStart_3847207 baseEnd_3847207 := by
    simpa [prefixWord, tailWord_3847207, baseEnd_3847207] using wordTrace_append hprefix tailTrace_3847207
  have hstable : (prefixWord ++ tailWord_3847207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847207).length < 2 ^ (prefixWord ++ tailWord_3847207).sum := by decide
  have hdescent : baseEnd_3847207 < baseStart_3847207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847237 : List Nat := [1, 3, 1, 1, 1, 3, 3, 5, 5]
def baseStart_3847237 : Nat := 118140960795 + 3847237 * 2 ^ 59
def prefixEnd_3847237 : Nat := 4983230072969 + 3 ^ 40 * 3847237 * 2
def baseEnd_3847237 : Nat := 219497974751296600138265

theorem tailTrace_3847237 : CollatzResearch.WordTrace tailWord_3847237 prefixEnd_3847237 219497974751296600138265 := by
  unfold tailWord_3847237
  simp only [CollatzResearch.WordTrace]
  refine ⟨140320261163124879613827965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93546840775416586409218643 140320261163124879613827965)
  ·
    refine ⟨52620097936171829855185487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140320261163124879613827965 52620097936171829855185487)
    ·
      refine ⟨78930146904257744782778231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52620097936171829855185487 78930146904257744782778231)
      ·
        refine ⟨118395220356386617174167347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78930146904257744782778231 118395220356386617174167347)
        ·
          refine ⟨177592830534579925761251021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118395220356386617174167347 177592830534579925761251021)
          ·
            refine ⟨66597311450467472160469133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177592830534579925761251021 66597311450467472160469133)
            ·
              refine ⟨24973991793925302060175925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66597311450467472160469133 24973991793925302060175925)
              ·
                refine ⟨2341311730680497068141493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24973991793925302060175925 2341311730680497068141493)
                ·
                  refine ⟨219497974751296600138265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2341311730680497068141493 219497974751296600138265)
                  ·
                    rfl

theorem cell23_3847237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_3847237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847237 prefixEnd_3847237 := by exact prefixLift 3847237
  have htrace : WordTrace (prefixWord ++ tailWord_3847237) baseStart_3847237 baseEnd_3847237 := by
    simpa [prefixWord, tailWord_3847237, baseEnd_3847237] using wordTrace_append hprefix tailTrace_3847237
  have hstable : (prefixWord ++ tailWord_3847237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847237).length < 2 ^ (prefixWord ++ tailWord_3847237).sum := by decide
  have hdescent : baseEnd_3847237 < baseStart_3847237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847257 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 2, 5, 2]
def baseStart_3847257 : Nat := 118140960795 + 3847257 * 2 ^ 59
def prefixEnd_3847257 : Nat := 4983230072969 + 3 ^ 40 * 3847257 * 2
def baseEnd_3847257 : Nat := 1975492042374759322994293

theorem tailTrace_3847257 : CollatzResearch.WordTrace tailWord_3847257 prefixEnd_3847257 1975492042374759322994293 := by
  unfold tailWord_3847257
  simp only [CollatzResearch.WordTrace]
  refine ⟨140320990623052423029556025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93547327082034948686370683 140320990623052423029556025)
  ·
    refine ⟨105240742967289317272167019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140320990623052423029556025 105240742967289317272167019)
    ·
      refine ⟨157861114450933975908250529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105240742967289317272167019 157861114450933975908250529)
      ·
        refine ⟨118395835838200481931187897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157861114450933975908250529 118395835838200481931187897)
        ·
          refine ⟨88796876878650361448390923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118395835838200481931187897 88796876878650361448390923)
          ·
            refine ⟨133195315317975542172586385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88796876878650361448390923 133195315317975542172586385)
            ·
              refine ⟨99896486488481656629439789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133195315317975542172586385 99896486488481656629439789)
              ·
                refine ⟨37461182433180621236039921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99896486488481656629439789 37461182433180621236039921)
                ·
                  refine ⟨28095886824885465927029941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37461182433180621236039921 28095886824885465927029941)
                  ·
                    refine ⟨2633989389833012430659057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28095886824885465927029941 2633989389833012430659057)
                    ·
                      refine ⟨1975492042374759322994293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2633989389833012430659057 1975492042374759322994293)
                      ·
                        rfl

theorem cell23_3847257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_3847257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847257 prefixEnd_3847257 := by exact prefixLift 3847257
  have htrace : WordTrace (prefixWord ++ tailWord_3847257) baseStart_3847257 baseEnd_3847257 := by
    simpa [prefixWord, tailWord_3847257, baseEnd_3847257] using wordTrace_append hprefix tailTrace_3847257
  have hstable : (prefixWord ++ tailWord_3847257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847257).length < 2 ^ (prefixWord ++ tailWord_3847257).sum := by decide
  have hdescent : baseEnd_3847257 < baseStart_3847257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847280 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 2, 8]
def baseStart_3847280 : Nat := 118140960795 + 3847280 * 2 ^ 59
def prefixEnd_3847280 : Nat := 4983230072969 + 3 ^ 40 * 3847280 * 2
def baseEnd_3847280 : Nat := 658501284143270911002229

theorem tailTrace_3847280 : CollatzResearch.WordTrace tailWord_3847280 prefixEnd_3847280 658501284143270911002229 := by
  unfold tailWord_3847280
  simp only [CollatzResearch.WordTrace]
  refine ⟨70160914750984548978821647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93547886334646065305095529 70160914750984548978821647)
  ·
    refine ⟨105241372126476823468232471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70160914750984548978821647 105241372126476823468232471)
    ·
      refine ⟨157862058189715235202348707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105241372126476823468232471 157862058189715235202348707)
      ·
        refine ⟨236793087284572852803523061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157862058189715235202348707 236793087284572852803523061)
        ·
          refine ⟨22199351932928704950330287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236793087284572852803523061 22199351932928704950330287)
          ·
            refine ⟨33299027899393057425495431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22199351932928704950330287 33299027899393057425495431)
            ·
              refine ⟨49948541849089586138243147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33299027899393057425495431 49948541849089586138243147)
              ·
                refine ⟨74922812773634379207364721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49948541849089586138243147 74922812773634379207364721)
                ·
                  refine ⟨56192109580225784405523541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74922812773634379207364721 56192109580225784405523541)
                  ·
                    refine ⟨658501284143270911002229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56192109580225784405523541 658501284143270911002229)
                    ·
                      rfl

theorem cell23_3847280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_3847280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847280 prefixEnd_3847280 := by exact prefixLift 3847280
  have htrace : WordTrace (prefixWord ++ tailWord_3847280) baseStart_3847280 baseEnd_3847280 := by
    simpa [prefixWord, tailWord_3847280, baseEnd_3847280] using wordTrace_append hprefix tailTrace_3847280
  have hstable : (prefixWord ++ tailWord_3847280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847280).length < 2 ^ (prefixWord ++ tailWord_3847280).sum := by decide
  have hdescent : baseEnd_3847280 < baseStart_3847280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847287 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_3847287 : Nat := 118140960795 + 3847287 * 2 ^ 59
def prefixEnd_3847287 : Nat := 4983230072969 + 3 ^ 40 * 3847287 * 2
def baseEnd_3847287 : Nat := 1975507446794394205619155

theorem tailTrace_3847287 : CollatzResearch.WordTrace tailWord_3847287 prefixEnd_3847287 1975507446794394205619155 := by
  unfold tailWord_3847287
  simp only [CollatzResearch.WordTrace]
  refine ⟨140322084812943738153148115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93548056541962492102098743 140322084812943738153148115)
  ·
    refine ⟨210483127219415607229722173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140322084812943738153148115 210483127219415607229722173)
    ·
      refine ⟨78931172707280852711145815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210483127219415607229722173 78931172707280852711145815)
      ·
        refine ⟨118396759060921279066718723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78931172707280852711145815 118396759060921279066718723)
        ·
          refine ⟨177595138591381918600078085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118396759060921279066718723 177595138591381918600078085)
          ·
            refine ⟨33299088485884109737514641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177595138591381918600078085 33299088485884109737514641)
            ·
              refine ⟨24974316364413082303135981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33299088485884109737514641 24974316364413082303135981)
              ·
                refine ⟨9365368636654905863675993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24974316364413082303135981 9365368636654905863675993)
                ·
                  refine ⟨7024026477491179397756995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9365368636654905863675993 7024026477491179397756995)
                  ·
                    refine ⟨10536039716236769096635493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7024026477491179397756995 10536039716236769096635493)
                    ·
                      refine ⟨1975507446794394205619155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10536039716236769096635493 1975507446794394205619155)
                      ·
                        rfl

theorem cell23_3847287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_3847287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847287 prefixEnd_3847287 := by exact prefixLift 3847287
  have htrace : WordTrace (prefixWord ++ tailWord_3847287) baseStart_3847287 baseEnd_3847287 := by
    simpa [prefixWord, tailWord_3847287, baseEnd_3847287] using wordTrace_append hprefix tailTrace_3847287
  have hstable : (prefixWord ++ tailWord_3847287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847287).length < 2 ^ (prefixWord ++ tailWord_3847287).sum := by decide
  have hdescent : baseEnd_3847287 < baseStart_3847287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847361 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 6]
def baseStart_3847361 : Nat := 118140960795 + 3847361 * 2 ^ 59
def prefixEnd_3847361 : Nat := 4983230072969 + 3 ^ 40 * 3847361 * 2
def baseEnd_3847361 : Nat := 219505049373647435121535

theorem tailTrace_3847361 : CollatzResearch.WordTrace tailWord_3847361 prefixEnd_3847361 219505049373647435121535 := by
  unfold tailWord_3847361
  simp only [CollatzResearch.WordTrace]
  refine ⟨140324783814675648791341937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93549855876450432527561291 140324783814675648791341937)
  ·
    refine ⟨105243587861006736593506453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140324783814675648791341937 105243587861006736593506453)
    ·
      refine ⟨4933293180984690777820615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105243587861006736593506453 4933293180984690777820615)
      ·
        refine ⟨7399939771477036166730923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4933293180984690777820615 7399939771477036166730923)
        ·
          refine ⟨11099909657215554250096385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399939771477036166730923 11099909657215554250096385)
          ·
            refine ⟨8324932242911665687572289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11099909657215554250096385 8324932242911665687572289)
            ·
              refine ⟨6243699182183749265679217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8324932242911665687572289 6243699182183749265679217)
              ·
                refine ⟨4682774386637811949259413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6243699182183749265679217 4682774386637811949259413)
                ·
                  refine ⟨219505049373647435121535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4682774386637811949259413 219505049373647435121535)
                  ·
                    rfl

theorem cell23_3847361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 6].length) (baseStart_3847361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847361 prefixEnd_3847361 := by exact prefixLift 3847361
  have htrace : WordTrace (prefixWord ++ tailWord_3847361) baseStart_3847361 baseEnd_3847361 := by
    simpa [prefixWord, tailWord_3847361, baseEnd_3847361] using wordTrace_append hprefix tailTrace_3847361
  have hstable : (prefixWord ++ tailWord_3847361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847361).length < 2 ^ (prefixWord ++ tailWord_3847361).sum := by decide
  have hdescent : baseEnd_3847361 < baseStart_3847361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847405 : List Nat := [1, 5, 1, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_3847405 : Nat := 118140960795 + 3847405 * 2 ^ 59
def prefixEnd_3847405 : Nat := 4983230072969 + 3 ^ 40 * 3847405 * 2
def baseEnd_3847405 : Nat := 1975568037511624743943613

theorem tailTrace_3847405 : CollatzResearch.WordTrace tailWord_3847405 prefixEnd_3847405 1975568037511624743943613 := by
  unfold tailWord_3847405
  simp only [CollatzResearch.WordTrace]
  refine ⟨140326388626516244305943669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93550925751010829537295779 140326388626516244305943669)
  ·
    refine ⟨13155598933735897903682219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140326388626516244305943669 13155598933735897903682219)
    ·
      refine ⟨19733398400603846855523329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13155598933735897903682219 19733398400603846855523329)
      ·
        refine ⟨14800048800452885141642497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19733398400603846855523329 14800048800452885141642497)
        ·
          refine ⟨11100036600339663856231873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14800048800452885141642497 11100036600339663856231873)
          ·
            refine ⟨8325027450254747892173905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11100036600339663856231873 8325027450254747892173905)
            ·
              refine ⟨6243770587691060919130429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8325027450254747892173905 6243770587691060919130429)
              ·
                refine ⟨2341413970384147844673911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6243770587691060919130429 2341413970384147844673911)
                ·
                  refine ⟨3512120955576221767010867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341413970384147844673911 3512120955576221767010867)
                  ·
                    refine ⟨5268181433364332650516301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3512120955576221767010867 5268181433364332650516301)
                    ·
                      refine ⟨1975568037511624743943613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5268181433364332650516301 1975568037511624743943613)
                      ·
                        rfl

theorem cell23_3847405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_3847405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847405 prefixEnd_3847405 := by exact prefixLift 3847405
  have htrace : WordTrace (prefixWord ++ tailWord_3847405) baseStart_3847405 baseEnd_3847405 := by
    simpa [prefixWord, tailWord_3847405, baseEnd_3847405] using wordTrace_append hprefix tailTrace_3847405
  have hstable : (prefixWord ++ tailWord_3847405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847405).length < 2 ^ (prefixWord ++ tailWord_3847405).sum := by decide
  have hdescent : baseEnd_3847405 < baseStart_3847405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847411 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 1, 1, 4]
def baseStart_3847411 : Nat := 118140960795 + 3847411 * 2 ^ 59
def prefixEnd_3847411 : Nat := 4983230072969 + 3 ^ 40 * 3847411 * 2
def baseEnd_3847411 : Nat := 1975571118395551720468585

theorem tailTrace_3847411 : CollatzResearch.WordTrace tailWord_3847411 prefixEnd_3847411 1975571118395551720468585 := by
  unfold tailWord_3847411
  simp only [CollatzResearch.WordTrace]
  refine ⟨140326607464494507330662087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93551071642996338220441391 140326607464494507330662087)
  ·
    refine ⟨210489911196741760995993131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140326607464494507330662087 210489911196741760995993131)
    ·
      refine ⟨315734866795112641493989697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210489911196741760995993131 315734866795112641493989697)
      ·
        refine ⟨236801150096334481120492273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315734866795112641493989697 236801150096334481120492273)
        ·
          refine ⟨177600862572250860840369205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236801150096334481120492273 177600862572250860840369205)
          ·
            refine ⟨16650080866148518203784613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177600862572250860840369205 16650080866148518203784613)
            ·
              refine ⟨3121890162402847163209615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16650080866148518203784613 3121890162402847163209615)
              ·
                refine ⟨4682835243604270744814423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121890162402847163209615 4682835243604270744814423)
                ·
                  refine ⟨7024252865406406117221635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682835243604270744814423 7024252865406406117221635)
                  ·
                    refine ⟨10536379298109609175832453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7024252865406406117221635 10536379298109609175832453)
                    ·
                      refine ⟨1975571118395551720468585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10536379298109609175832453 1975571118395551720468585)
                      ·
                        rfl

theorem cell23_3847411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 1, 4].length) (baseStart_3847411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847411 prefixEnd_3847411 := by exact prefixLift 3847411
  have htrace : WordTrace (prefixWord ++ tailWord_3847411) baseStart_3847411 baseEnd_3847411 := by
    simpa [prefixWord, tailWord_3847411, baseEnd_3847411] using wordTrace_append hprefix tailTrace_3847411
  have hstable : (prefixWord ++ tailWord_3847411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847411).length < 2 ^ (prefixWord ++ tailWord_3847411).sum := by decide
  have hdescent : baseEnd_3847411 < baseStart_3847411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847412 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 6]
def baseStart_3847412 : Nat := 118140960795 + 3847412 * 2 ^ 59
def prefixEnd_3847412 : Nat := 4983230072969 + 3 ^ 40 * 3847412 * 2
def baseEnd_3847412 : Nat := 219507959097356246284009

theorem tailTrace_3847412 : CollatzResearch.WordTrace tailWord_3847412 prefixEnd_3847412 219507959097356246284009 := by
  unfold tailWord_3847412
  simp only [CollatzResearch.WordTrace]
  refine ⟨70163321968745442250724245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93551095958327256334298993 70163321968745442250724245)
  ·
    refine ⟨3288905717284942605502699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70163321968745442250724245 3288905717284942605502699)
    ·
      refine ⟨4933358575927413908254049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288905717284942605502699 4933358575927413908254049)
      ·
        refine ⟨3700018931945560431190537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4933358575927413908254049 3700018931945560431190537)
        ·
          refine ⟨2775014198959170323392903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3700018931945560431190537 2775014198959170323392903)
          ·
            refine ⟨4162521298438755485089355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775014198959170323392903 4162521298438755485089355)
            ·
              refine ⟨6243781947658133227634033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162521298438755485089355 6243781947658133227634033)
              ·
                refine ⟨4682836460743599920725525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6243781947658133227634033 4682836460743599920725525)
                ·
                  refine ⟨219507959097356246284009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4682836460743599920725525 219507959097356246284009)
                  ·
                    rfl

theorem cell23_3847412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_3847412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847412 prefixEnd_3847412 := by exact prefixLift 3847412
  have htrace : WordTrace (prefixWord ++ tailWord_3847412) baseStart_3847412 baseEnd_3847412 := by
    simpa [prefixWord, tailWord_3847412, baseEnd_3847412] using wordTrace_append hprefix tailTrace_3847412
  have hstable : (prefixWord ++ tailWord_3847412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847412).length < 2 ^ (prefixWord ++ tailWord_3847412).sum := by decide
  have hdescent : baseEnd_3847412 < baseStart_3847412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847414 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3847414 : Nat := 118140960795 + 3847414 * 2 ^ 59
def prefixEnd_3847414 : Nat := 4983230072969 + 3 ^ 40 * 3847414 * 2
def baseEnd_3847414 : Nat := 1975572658837515208731071

theorem tailTrace_3847414 : CollatzResearch.WordTrace tailWord_3847414 prefixEnd_3847414 1975572658837515208731071 := by
  unfold tailWord_3847414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770419805217727427688831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93551144588989092562014197 8770419805217727427688831)
  ·
    refine ⟨13155629707826591141533247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770419805217727427688831 13155629707826591141533247)
    ·
      refine ⟨19733444561739886712299871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13155629707826591141533247 19733444561739886712299871)
      ·
        refine ⟨29600166842609830068449807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19733444561739886712299871 29600166842609830068449807)
        ·
          refine ⟨44400250263914745102674711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29600166842609830068449807 44400250263914745102674711)
          ·
            refine ⟨66600375395872117654012067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44400250263914745102674711 66600375395872117654012067)
            ·
              refine ⟨99900563093808176481018101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66600375395872117654012067 99900563093808176481018101)
              ·
                refine ⟨9365677790044516545095447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99900563093808176481018101 9365677790044516545095447)
                ·
                  refine ⟨14048516685066774817643171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9365677790044516545095447 14048516685066774817643171)
                  ·
                    refine ⟨21072775027600162226464757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14048516685066774817643171 21072775027600162226464757)
                    ·
                      refine ⟨1975572658837515208731071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21072775027600162226464757 1975572658837515208731071)
                      ·
                        rfl

theorem cell23_3847414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3847414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847414 prefixEnd_3847414 := by exact prefixLift 3847414
  have htrace : WordTrace (prefixWord ++ tailWord_3847414) baseStart_3847414 baseEnd_3847414 := by
    simpa [prefixWord, tailWord_3847414, baseEnd_3847414] using wordTrace_append hprefix tailTrace_3847414
  have hstable : (prefixWord ++ tailWord_3847414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847414).length < 2 ^ (prefixWord ++ tailWord_3847414).sum := by decide
  have hdescent : baseEnd_3847414 < baseStart_3847414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847428 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_3847428 : Nat := 118140960795 + 3847428 * 2 ^ 59
def prefixEnd_3847428 : Nat := 4983230072969 + 3 ^ 40 * 3847428 * 2
def baseEnd_3847428 : Nat := 1975579847566678153956007

theorem tailTrace_3847428 : CollatzResearch.WordTrace tailWord_3847428 prefixEnd_3847428 1975579847566678153956007 := by
  unfold tailWord_3847428
  simp only [CollatzResearch.WordTrace]
  refine ⟨70163613752716459617015469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93551485003621946156020625 70163613752716459617015469)
  ·
    refine ⟨26311355157268672356380801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70163613752716459617015469 26311355157268672356380801)
    ·
      refine ⟨19733516367951504267285601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26311355157268672356380801 19733516367951504267285601)
      ·
        refine ⟨14800137275963628200464201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19733516367951504267285601 14800137275963628200464201)
        ·
          refine ⟨11100102956972721150348151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14800137275963628200464201 11100102956972721150348151)
          ·
            refine ⟨16650154435459081725522227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100102956972721150348151 16650154435459081725522227)
            ·
              refine ⟨24975231653188622588283341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16650154435459081725522227 24975231653188622588283341)
              ·
                refine ⟨9365711869945733470606253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24975231653188622588283341 9365711869945733470606253)
                ·
                  refine ⟨3512141951229650051477345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9365711869945733470606253 3512141951229650051477345)
                  ·
                    refine ⟨2634106463422237538608009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3512141951229650051477345 2634106463422237538608009)
                    ·
                      refine ⟨1975579847566678153956007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634106463422237538608009 1975579847566678153956007)
                      ·
                        rfl

theorem cell23_3847428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_3847428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847428 prefixEnd_3847428 := by exact prefixLift 3847428
  have htrace : WordTrace (prefixWord ++ tailWord_3847428) baseStart_3847428 baseEnd_3847428 := by
    simpa [prefixWord, tailWord_3847428, baseEnd_3847428] using wordTrace_append hprefix tailTrace_3847428
  have hstable : (prefixWord ++ tailWord_3847428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847428).length < 2 ^ (prefixWord ++ tailWord_3847428).sum := by decide
  have hdescent : baseEnd_3847428 < baseStart_3847428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847438 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_3847438 : Nat := 118140960795 + 3847438 * 2 ^ 59
def prefixEnd_3847438 : Nat := 4983230072969 + 3 ^ 40 * 3847438 * 2
def baseEnd_3847438 : Nat := 658528327457741038276987

theorem tailTrace_3847438 : CollatzResearch.WordTrace tailWord_3847438 prefixEnd_3847438 658528327457741038276987 := by
  unfold tailWord_3847438
  simp only [CollatzResearch.WordTrace]
  refine ⟨17540949029424586367736871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93551728156931127294596645 17540949029424586367736871)
  ·
    refine ⟨26311423544136879551605307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17540949029424586367736871 26311423544136879551605307)
    ·
      refine ⟨39467135316205319327407961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26311423544136879551605307 39467135316205319327407961)
      ·
        refine ⟨29600351487153989495555971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39467135316205319327407961 29600351487153989495555971)
        ·
          refine ⟨44400527230730984243333957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29600351487153989495555971 44400527230730984243333957)
          ·
            refine ⟨8325098855762059545625117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44400527230730984243333957 8325098855762059545625117)
            ·
              refine ⟨3121912070910772329609419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8325098855762059545625117 3121912070910772329609419)
              ·
                refine ⟨4682868106366158494414129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121912070910772329609419 4682868106366158494414129)
                ·
                  refine ⟨3512151079774618870810597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4682868106366158494414129 3512151079774618870810597)
                  ·
                    refine ⟨658528327457741038276987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3512151079774618870810597 658528327457741038276987)
                    ·
                      rfl

theorem cell23_3847438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_3847438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847438 prefixEnd_3847438 := by exact prefixLift 3847438
  have htrace : WordTrace (prefixWord ++ tailWord_3847438) baseStart_3847438 baseEnd_3847438 := by
    simpa [prefixWord, tailWord_3847438, baseEnd_3847438] using wordTrace_append hprefix tailTrace_3847438
  have hstable : (prefixWord ++ tailWord_3847438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847438).length < 2 ^ (prefixWord ++ tailWord_3847438).sum := by decide
  have hdescent : baseEnd_3847438 < baseStart_3847438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847461 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 3]
def baseStart_3847461 : Nat := 118140960795 + 3847461 * 2 ^ 59
def prefixEnd_3847461 : Nat := 4983230072969 + 3 ^ 40 * 3847461 * 2
def baseEnd_3847461 : Nat := 1975596792428276524843355

theorem tailTrace_3847461 : CollatzResearch.WordTrace tailWord_3847461 prefixEnd_3847461 1975596792428276524843355 := by
  unfold tailWord_3847461
  simp only [CollatzResearch.WordTrace]
  refine ⟨140328431114313365869982237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93552287409542243913321491 140328431114313365869982237)
  ·
    refine ⟨52623161667867512201243339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140328431114313365869982237 52623161667867512201243339)
    ·
      refine ⟨78934742501801268301865009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52623161667867512201243339 78934742501801268301865009)
      ·
        refine ⟨59201056876350951226398757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78934742501801268301865009 59201056876350951226398757)
        ·
          refine ⟨11100198164315803354949767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59201056876350951226398757 11100198164315803354949767)
          ·
            refine ⟨16650297246473705032424651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100198164315803354949767 16650297246473705032424651)
            ·
              refine ⟨24975445869710557548636977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16650297246473705032424651 24975445869710557548636977)
              ·
                refine ⟨18731584402282918161477733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24975445869710557548636977 18731584402282918161477733)
                ·
                  refine ⟨3512172075428047155277075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18731584402282918161477733 3512172075428047155277075)
                  ·
                    refine ⟨5268258113142070732915613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3512172075428047155277075 5268258113142070732915613)
                    ·
                      refine ⟨1975596792428276524843355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5268258113142070732915613 1975596792428276524843355)
                      ·
                        rfl

theorem cell23_3847461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_3847461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847461 prefixEnd_3847461 := by exact prefixLift 3847461
  have htrace : WordTrace (prefixWord ++ tailWord_3847461) baseStart_3847461 baseEnd_3847461 := by
    simpa [prefixWord, tailWord_3847461, baseEnd_3847461] using wordTrace_append hprefix tailTrace_3847461
  have hstable : (prefixWord ++ tailWord_3847461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847461).length < 2 ^ (prefixWord ++ tailWord_3847461).sum := by decide
  have hdescent : baseEnd_3847461 < baseStart_3847461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847467 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 4]
def baseStart_3847467 : Nat := 118140960795 + 3847467 * 2 ^ 59
def prefixEnd_3847467 : Nat := 4983230072969 + 3 ^ 40 * 3847467 * 2
def baseEnd_3847467 : Nat := 1975599873312203501368327

theorem tailTrace_3847467 : CollatzResearch.WordTrace tailWord_3847467 prefixEnd_3847467 1975599873312203501368327 := by
  unfold tailWord_3847467
  simp only [CollatzResearch.WordTrace]
  refine ⟨140328649952291628894700655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93552433301527752596467103 140328649952291628894700655)
  ·
    refine ⟨210492974928437443342050983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140328649952291628894700655 210492974928437443342050983)
    ·
      refine ⟨315739462392656165013076475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210492974928437443342050983 315739462392656165013076475)
      ·
        refine ⟨473609193588984247519614713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315739462392656165013076475 473609193588984247519614713)
        ·
          refine ⟨355206895191738185639711035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473609193588984247519614713 355206895191738185639711035)
          ·
            refine ⟨532810342787607278459566553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355206895191738185639711035 532810342787607278459566553)
            ·
              refine ⟨399607757090705458844674915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532810342787607278459566553 399607757090705458844674915)
              ·
                refine ⟨599411635636058188267012373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399607757090705458844674915 599411635636058188267012373)
                ·
                  refine ⟨28097420420440227575016205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 599411635636058188267012373 28097420420440227575016205)
                  ·
                    refine ⟨10536532657665085340631077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28097420420440227575016205 10536532657665085340631077)
                    ·
                      refine ⟨1975599873312203501368327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10536532657665085340631077 1975599873312203501368327)
                      ·
                        rfl

theorem cell23_3847467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 4].length) (baseStart_3847467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847467 prefixEnd_3847467 := by exact prefixLift 3847467
  have htrace : WordTrace (prefixWord ++ tailWord_3847467) baseStart_3847467 baseEnd_3847467 := by
    simpa [prefixWord, tailWord_3847467, baseEnd_3847467] using wordTrace_append hprefix tailTrace_3847467
  have hstable : (prefixWord ++ tailWord_3847467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847467).length < 2 ^ (prefixWord ++ tailWord_3847467).sum := by decide
  have hdescent : baseEnd_3847467 < baseStart_3847467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847495 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_3847495 : Nat := 118140960795 + 3847495 * 2 ^ 59
def prefixEnd_3847495 : Nat := 4983230072969 + 3 ^ 40 * 3847495 * 2
def baseEnd_3847495 : Nat := 1975614250770529391818199

theorem tailTrace_3847495 : CollatzResearch.WordTrace tailWord_3847495 prefixEnd_3847495 1975614250770529391818199 := by
  unfold tailWord_3847495
  simp only [CollatzResearch.WordTrace]
  refine ⟨140329671196190189676719939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93553114130793459784479959 140329671196190189676719939)
  ·
    refine ⟨210494506794285284515079909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140329671196190189676719939 210494506794285284515079909)
    ·
      refine ⟨39467720023928490846577483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210494506794285284515079909 39467720023928490846577483)
      ·
        refine ⟨59201580035892736269866225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39467720023928490846577483 59201580035892736269866225)
        ·
          refine ⟨44401185026919552202399669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59201580035892736269866225 44401185026919552202399669)
          ·
            refine ⟨4162611096273708018974969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44401185026919552202399669 4162611096273708018974969)
            ·
              refine ⟨3121958322205281014231227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4162611096273708018974969 3121958322205281014231227)
              ·
                refine ⟨4682937483307921521346841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3121958322205281014231227 4682937483307921521346841)
                ·
                  refine ⟨3512203112480941141010131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4682937483307921521346841 3512203112480941141010131)
                  ·
                    refine ⟨5268304668721411711515197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3512203112480941141010131 5268304668721411711515197)
                    ·
                      refine ⟨1975614250770529391818199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5268304668721411711515197 1975614250770529391818199)
                      ·
                        rfl

theorem cell23_3847495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_3847495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847495 prefixEnd_3847495 := by exact prefixLift 3847495
  have htrace : WordTrace (prefixWord ++ tailWord_3847495) baseStart_3847495 baseEnd_3847495 := by
    simpa [prefixWord, tailWord_3847495, baseEnd_3847495] using wordTrace_append hprefix tailTrace_3847495
  have hstable : (prefixWord ++ tailWord_3847495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847495).length < 2 ^ (prefixWord ++ tailWord_3847495).sum := by decide
  have hdescent : baseEnd_3847495 < baseStart_3847495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847507 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 9]
def baseStart_3847507 : Nat := 118140960795 + 3847507 * 2 ^ 59
def prefixEnd_3847507 : Nat := 4983230072969 + 3 ^ 40 * 3847507 * 2
def baseEnd_3847507 : Nat := 219513379170931482763127

theorem tailTrace_3847507 : CollatzResearch.WordTrace tailWord_3847507 prefixEnd_3847507 219513379170931482763127 := by
  unfold tailWord_3847507
  simp only [CollatzResearch.WordTrace]
  refine ⟨140330108872146715726156775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93553405914764477150771183 140330108872146715726156775)
  ·
    refine ⟨210495163308220073589235163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140330108872146715726156775 210495163308220073589235163)
    ·
      refine ⟨315742744962330110383852745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210495163308220073589235163 315742744962330110383852745)
      ·
        refine ⟨236807058721747582787889559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315742744962330110383852745 236807058721747582787889559)
        ·
          refine ⟨355210588082621374181834339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236807058721747582787889559 355210588082621374181834339)
          ·
            refine ⟨532815882123932061272751509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355210588082621374181834339 532815882123932061272751509)
            ·
              refine ⟨24975744474559315372160227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 532815882123932061272751509 24975744474559315372160227)
              ·
                refine ⟨37463616711838973058240341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24975744474559315372160227 37463616711838973058240341)
                ·
                  refine ⟨219513379170931482763127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37463616711838973058240341 219513379170931482763127)
                  ·
                    rfl

theorem cell23_3847507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 9].length) (baseStart_3847507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847507 prefixEnd_3847507 := by exact prefixLift 3847507
  have htrace : WordTrace (prefixWord ++ tailWord_3847507) baseStart_3847507 baseEnd_3847507 := by
    simpa [prefixWord, tailWord_3847507, baseEnd_3847507] using wordTrace_append hprefix tailTrace_3847507
  have hstable : (prefixWord ++ tailWord_3847507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847507).length < 2 ^ (prefixWord ++ tailWord_3847507).sum := by decide
  have hdescent : baseEnd_3847507 < baseStart_3847507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847591 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3847591 : Nat := 118140960795 + 3847591 * 2 ^ 59
def prefixEnd_3847591 : Nat := 4983230072969 + 3 ^ 40 * 3847591 * 2
def baseEnd_3847591 : Nat := 1975663544913361016217757

theorem tailTrace_3847591 : CollatzResearch.WordTrace tailWord_3847591 prefixEnd_3847591 1975663544913361016217757 := by
  unfold tailWord_3847591
  simp only [CollatzResearch.WordTrace]
  refine ⟨140333172603842398072214627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93555448402561598714809751 140333172603842398072214627)
  ·
    refine ⟨210499758905763597108321941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140333172603842398072214627 210499758905763597108321941)
    ·
      refine ⟨9867176198707668614452591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210499758905763597108321941 9867176198707668614452591)
      ·
        refine ⟨14800764298061502921678887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9867176198707668614452591 14800764298061502921678887)
        ·
          refine ⟨22201146447092254382518331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14800764298061502921678887 22201146447092254382518331)
          ·
            refine ⟨33301719670638381573777497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22201146447092254382518331 33301719670638381573777497)
            ·
              refine ⟨24976289752978786180333123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33301719670638381573777497 24976289752978786180333123)
              ·
                refine ⟨37464434629468179270499685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24976289752978786180333123 37464434629468179270499685)
                ·
                  refine ⟨7024581493025283613218691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37464434629468179270499685 7024581493025283613218691)
                  ·
                    refine ⟨10536872239537925419828037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7024581493025283613218691 10536872239537925419828037)
                    ·
                      refine ⟨1975663544913361016217757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10536872239537925419828037 1975663544913361016217757)
                      ·
                        rfl

theorem cell23_3847591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3847591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847591 prefixEnd_3847591 := by exact prefixLift 3847591
  have htrace : WordTrace (prefixWord ++ tailWord_3847591) baseStart_3847591 baseEnd_3847591 := by
    simpa [prefixWord, tailWord_3847591, baseEnd_3847591] using wordTrace_append hprefix tailTrace_3847591
  have hstable : (prefixWord ++ tailWord_3847591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847591).length < 2 ^ (prefixWord ++ tailWord_3847591).sum := by decide
  have hdescent : baseEnd_3847591 < baseStart_3847591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847704 : List Nat := [2, 1, 2, 3, 15]
def baseStart_3847704 : Nat := 118140960795 + 3847704 * 2 ^ 59
def prefixEnd_3847704 : Nat := 4983230072969 + 3 ^ 40 * 3847704 * 2
def baseEnd_3847704 : Nat := 2710180477678078290953

theorem tailTrace_3847704 : CollatzResearch.WordTrace tailWord_3847704 prefixEnd_3847704 2710180477678078290953 := by
  unfold tailWord_3847704
  simp only [CollatzResearch.WordTrace]
  refine ⟨70168647026216509185539083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93558196034955345580718777 70168647026216509185539083)
  ·
    refine ⟨105252970539324763778308625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70168647026216509185539083 105252970539324763778308625)
    ·
      refine ⟨78939727904493572833731469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105252970539324763778308625 78939727904493572833731469)
      ·
        refine ⟨29602397964185089812649301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78939727904493572833731469 29602397964185089812649301)
        ·
          refine ⟨2710180477678078290953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 29602397964185089812649301 2710180477678078290953)
          ·
            rfl

theorem cell23_3847704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 15].length) (baseStart_3847704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847704 prefixEnd_3847704 := by exact prefixLift 3847704
  have htrace : WordTrace (prefixWord ++ tailWord_3847704) baseStart_3847704 baseEnd_3847704 := by
    simpa [prefixWord, tailWord_3847704, baseEnd_3847704] using wordTrace_append hprefix tailTrace_3847704
  have hstable : (prefixWord ++ tailWord_3847704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847704).length < 2 ^ (prefixWord ++ tailWord_3847704).sum := by decide
  have hdescent : baseEnd_3847704 < baseStart_3847704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847791 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_3847791 : Nat := 118140960795 + 3847791 * 2 ^ 59
def prefixEnd_3847791 : Nat := 4983230072969 + 3 ^ 40 * 3847791 * 2
def baseEnd_3847791 : Nat := 1975766241044260233716837

theorem tailTrace_3847791 : CollatzResearch.WordTrace tailWord_3847791 prefixEnd_3847791 1975766241044260233716837 := by
  unfold tailWord_3847791
  simp only [CollatzResearch.WordTrace]
  refine ⟨140340467203117832229495227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93560311468745221486330151 140340467203117832229495227)
  ·
    refine ⟨210510700804676748344242841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140340467203117832229495227 210510700804676748344242841)
    ·
      refine ⟨157883025603507561258182131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210510700804676748344242841 157883025603507561258182131)
      ·
        refine ⟨236824538405261341887273197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157883025603507561258182131 236824538405261341887273197)
        ·
          refine ⟨88809201901973003207727449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236824538405261341887273197 88809201901973003207727449)
          ·
            refine ⟨66606901426479752405795587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88809201901973003207727449 66606901426479752405795587)
            ·
              refine ⟨99910352139719628608693381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66606901426479752405795587 99910352139719628608693381)
              ·
                refine ⟨18733191026197430364130009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99910352139719628608693381 18733191026197430364130009)
                ·
                  refine ⟨14049893269648072773097507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18733191026197430364130009 14049893269648072773097507)
                  ·
                    refine ⟨21074839904472109159646261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14049893269648072773097507 21074839904472109159646261)
                    ·
                      refine ⟨1975766241044260233716837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21074839904472109159646261 1975766241044260233716837)
                      ·
                        rfl

theorem cell23_3847791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_3847791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847791 prefixEnd_3847791 := by exact prefixLift 3847791
  have htrace : WordTrace (prefixWord ++ tailWord_3847791) baseStart_3847791 baseEnd_3847791 := by
    simpa [prefixWord, tailWord_3847791, baseEnd_3847791] using wordTrace_append hprefix tailTrace_3847791
  have hstable : (prefixWord ++ tailWord_3847791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847791).length < 2 ^ (prefixWord ++ tailWord_3847791).sum := by decide
  have hdescent : baseEnd_3847791 < baseStart_3847791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847792 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 1, 3, 2]
def baseStart_3847792 : Nat := 118140960795 + 3847792 * 2 ^ 59
def prefixEnd_3847792 : Nat := 4983230072969 + 3 ^ 40 * 3847792 * 2
def baseEnd_3847792 : Nat := 1975766754524914729804333

theorem tailTrace_3847792 : CollatzResearch.WordTrace tailWord_3847792 prefixEnd_3847792 1975766754524914729804333 := by
  unfold tailWord_3847792
  simp only [CollatzResearch.WordTrace]
  refine ⟨70170251838057104700140815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93560335784076139600187753 70170251838057104700140815)
  ·
    refine ⟨105255377757085657050211223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70170251838057104700140815 105255377757085657050211223)
    ·
      refine ⟨157883066635628485575316835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105255377757085657050211223 157883066635628485575316835)
      ·
        refine ⟨236824599953442728362975253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157883066635628485575316835 236824599953442728362975253)
        ·
          refine ⟨11101153122817627892014465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 236824599953442728362975253 11101153122817627892014465)
          ·
            refine ⟨8325864842113220919010849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11101153122817627892014465 8325864842113220919010849)
            ·
              refine ⟨6244398631584915689258137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8325864842113220919010849 6244398631584915689258137)
              ·
                refine ⟨4683298973688686766943603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6244398631584915689258137 4683298973688686766943603)
                ·
                  refine ⟨7024948460533030150415405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683298973688686766943603 7024948460533030150415405)
                  ·
                    refine ⟨2634355672699886306405777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7024948460533030150415405 2634355672699886306405777)
                    ·
                      refine ⟨1975766754524914729804333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634355672699886306405777 1975766754524914729804333)
                      ·
                        rfl

theorem cell23_3847792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 3, 2].length) (baseStart_3847792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847792 prefixEnd_3847792 := by exact prefixLift 3847792
  have htrace : WordTrace (prefixWord ++ tailWord_3847792) baseStart_3847792 baseEnd_3847792 := by
    simpa [prefixWord, tailWord_3847792, baseEnd_3847792] using wordTrace_append hprefix tailTrace_3847792
  have hstable : (prefixWord ++ tailWord_3847792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847792).length < 2 ^ (prefixWord ++ tailWord_3847792).sum := by decide
  have hdescent : baseEnd_3847792 < baseStart_3847792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847822 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_3847822 : Nat := 118140960795 + 3847822 * 2 ^ 59
def prefixEnd_3847822 : Nat := 4983230072969 + 3 ^ 40 * 3847822 * 2
def baseEnd_3847822 : Nat := 1975782158944549612429195

theorem tailTrace_3847822 : CollatzResearch.WordTrace tailWord_3847822 prefixEnd_3847822 1975782158944549612429195 := by
  unfold tailWord_3847822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17542699733250690565484215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93561065244003683015915813 17542699733250690565484215)
  ·
    refine ⟨26314049599876035848226323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17542699733250690565484215 26314049599876035848226323)
    ·
      refine ⟨39471074399814053772339485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26314049599876035848226323 39471074399814053772339485)
      ·
        refine ⟨14801652899930270164627307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39471074399814053772339485 14801652899930270164627307)
        ·
          refine ⟨22202479349895405246940961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14801652899930270164627307 22202479349895405246940961)
          ·
            refine ⟨16651859512421553935205721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22202479349895405246940961 16651859512421553935205721)
            ·
              refine ⟨12488894634316165451404291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16651859512421553935205721 12488894634316165451404291)
              ·
                refine ⟨18733341951474248177106437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12488894634316165451404291 18733341951474248177106437)
                ·
                  refine ⟨3512501615901421533207457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18733341951474248177106437 3512501615901421533207457)
                  ·
                    refine ⟨2634376211926066149905593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3512501615901421533207457 2634376211926066149905593)
                    ·
                      refine ⟨1975782158944549612429195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634376211926066149905593 1975782158944549612429195)
                      ·
                        rfl

theorem cell23_3847822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_3847822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847822 prefixEnd_3847822 := by exact prefixLift 3847822
  have htrace : WordTrace (prefixWord ++ tailWord_3847822) baseStart_3847822 baseEnd_3847822 := by
    simpa [prefixWord, tailWord_3847822, baseEnd_3847822] using wordTrace_append hprefix tailTrace_3847822
  have hstable : (prefixWord ++ tailWord_3847822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847822).length < 2 ^ (prefixWord ++ tailWord_3847822).sum := by decide
  have hdescent : baseEnd_3847822 < baseStart_3847822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847858 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_3847858 : Nat := 118140960795 + 3847858 * 2 ^ 59
def prefixEnd_3847858 : Nat := 4983230072969 + 3 ^ 40 * 3847858 * 2
def baseEnd_3847858 : Nat := 658600214749370490526343

theorem tailTrace_3847858 : CollatzResearch.WordTrace tailWord_3847858 prefixEnd_3847858 658600214749370490526343 := by
  unfold tailWord_3847858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35085727723468775668046057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93561940595916735114789485 35085727723468775668046057)
  ·
    refine ⟨26314295792601581751034543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35085727723468775668046057 26314295792601581751034543)
    ·
      refine ⟨39471443688902372626551815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26314295792601581751034543 39471443688902372626551815)
      ·
        refine ⟨59207165533353558939827723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39471443688902372626551815 59207165533353558939827723)
        ·
          refine ⟨88810748300030338409741585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59207165533353558939827723 88810748300030338409741585)
          ·
            refine ⟨66608061225022753807306189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88810748300030338409741585 66608061225022753807306189)
            ·
              refine ⟨24978022959383532677739821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66608061225022753807306189 24978022959383532677739821)
              ·
                refine ⟨9366758609768824754152433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24978022959383532677739821 9366758609768824754152433)
                ·
                  refine ⟨7025068957326618565614325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9366758609768824754152433 7025068957326618565614325)
                  ·
                    refine ⟨658600214749370490526343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7025068957326618565614325 658600214749370490526343)
                    ·
                      rfl

theorem cell23_3847858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_3847858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847858 prefixEnd_3847858 := by exact prefixLift 3847858
  have htrace : WordTrace (prefixWord ++ tailWord_3847858) baseStart_3847858 baseEnd_3847858 := by
    simpa [prefixWord, tailWord_3847858, baseEnd_3847858] using wordTrace_append hprefix tailTrace_3847858
  have hstable : (prefixWord ++ tailWord_3847858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847858).length < 2 ^ (prefixWord ++ tailWord_3847858).sum := by decide
  have hdescent : baseEnd_3847858 < baseStart_3847858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847868 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3847868 : Nat := 118140960795 + 3847868 * 2 ^ 59
def prefixEnd_3847868 : Nat := 4983230072969 + 3 ^ 40 * 3847868 * 2
def baseEnd_3847868 : Nat := 1975805779054656432453983

theorem tailTrace_3847868 : CollatzResearch.WordTrace tailWord_3847868 prefixEnd_3847868 1975805779054656432453983 := by
  unfold tailWord_3847868
  simp only [CollatzResearch.WordTrace]
  refine ⟨70171637811919437190024129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93562183749225916253365505 70171637811919437190024129)
  ·
    refine ⟨52628728358939577892518097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70171637811919437190024129 52628728358939577892518097)
    ·
      refine ⟨39471546269204683419388573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52628728358939577892518097 39471546269204683419388573)
      ·
        refine ⟨14801829850951756282270715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39471546269204683419388573 14801829850951756282270715)
        ·
          refine ⟨22202744776427634423406073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14801829850951756282270715 22202744776427634423406073)
          ·
            refine ⟨16652058582320725817554555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22202744776427634423406073 16652058582320725817554555)
            ·
              refine ⟨24978087873481088726331833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16652058582320725817554555 24978087873481088726331833)
              ·
                refine ⟨18733565905110816544748875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24978087873481088726331833 18733565905110816544748875)
                ·
                  refine ⟨28100348857666224817123313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18733565905110816544748875 28100348857666224817123313)
                  ·
                    refine ⟨21075261643249668612842485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28100348857666224817123313 21075261643249668612842485)
                    ·
                      refine ⟨1975805779054656432453983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21075261643249668612842485 1975805779054656432453983)
                      ·
                        rfl

theorem cell23_3847868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3847868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847868 prefixEnd_3847868 := by exact prefixLift 3847868
  have htrace : WordTrace (prefixWord ++ tailWord_3847868) baseStart_3847868 baseEnd_3847868 := by
    simpa [prefixWord, tailWord_3847868, baseEnd_3847868] using wordTrace_append hprefix tailTrace_3847868
  have hstable : (prefixWord ++ tailWord_3847868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847868).length < 2 ^ (prefixWord ++ tailWord_3847868).sum := by decide
  have hdescent : baseEnd_3847868 < baseStart_3847868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847895 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 2, 4, 2]
def baseStart_3847895 : Nat := 118140960795 + 3847895 * 2 ^ 59
def prefixEnd_3847895 : Nat := 4983230072969 + 3 ^ 40 * 3847895 * 2
def baseEnd_3847895 : Nat := 1975819643032327826816359

theorem tailTrace_3847895 : CollatzResearch.WordTrace tailWord_3847895 prefixEnd_3847895 1975819643032327826816359 := by
  unfold tailWord_3847895
  simp only [CollatzResearch.WordTrace]
  refine ⟨140344260394741057991281139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93562840263160705327520759 140344260394741057991281139)
  ·
    refine ⟨210516390592111586986921709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140344260394741057991281139 210516390592111586986921709)
    ·
      refine ⟨78943646472041845120095641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210516390592111586986921709 78943646472041845120095641)
      ·
        refine ⟨59207734854031383840071731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78943646472041845120095641 59207734854031383840071731)
        ·
          refine ⟨88811602281047075760107597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59207734854031383840071731 88811602281047075760107597)
          ·
            refine ⟨33304350855392653410040349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88811602281047075760107597 33304350855392653410040349)
            ·
              refine ⟨12489131570772245028765131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33304350855392653410040349 12489131570772245028765131)
              ·
                refine ⟨18733697356158367543147697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489131570772245028765131 18733697356158367543147697)
                ·
                  refine ⟨14050273017118775657360773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18733697356158367543147697 14050273017118775657360773)
                  ·
                    refine ⟨2634426190709770435755145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14050273017118775657360773 2634426190709770435755145)
                    ·
                      refine ⟨1975819643032327826816359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634426190709770435755145 1975819643032327826816359)
                      ·
                        rfl

theorem cell23_3847895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_3847895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847895 prefixEnd_3847895 := by exact prefixLift 3847895
  have htrace : WordTrace (prefixWord ++ tailWord_3847895) baseStart_3847895 baseEnd_3847895 := by
    simpa [prefixWord, tailWord_3847895, baseEnd_3847895] using wordTrace_append hprefix tailTrace_3847895
  have hstable : (prefixWord ++ tailWord_3847895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847895).length < 2 ^ (prefixWord ++ tailWord_3847895).sum := by decide
  have hdescent : baseEnd_3847895 < baseStart_3847895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847912 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3847912 : Nat := 118140960795 + 3847912 * 2 ^ 59
def prefixEnd_3847912 : Nat := 4983230072969 + 3 ^ 40 * 3847912 * 2
def baseEnd_3847912 : Nat := 1975828372203454260303781

theorem tailTrace_3847912 : CollatzResearch.WordTrace tailWord_3847912 prefixEnd_3847912 1975828372203454260303781 := by
  unfold tailWord_3847912
  simp only [CollatzResearch.WordTrace]
  refine ⟨70172440217839734947324995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93563253623786313263099993 70172440217839734947324995)
  ·
    refine ⟨105258660326759602420987493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70172440217839734947324995 105258660326759602420987493)
    ·
      refine ⟨19735998811267425453935155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105258660326759602420987493 19735998811267425453935155)
      ·
        refine ⟨29603998216901138180902733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19735998811267425453935155 29603998216901138180902733)
        ·
          refine ⟨11101499331337926817838525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29603998216901138180902733 11101499331337926817838525)
          ·
            refine ⟨4163062249251722556689447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11101499331337926817838525 4163062249251722556689447)
            ·
              refine ⟨6244593373877583835034171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163062249251722556689447 6244593373877583835034171)
              ·
                refine ⟨9366890060816375752551257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244593373877583835034171 9366890060816375752551257)
                ·
                  refine ⟨7025167545612281814413443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9366890060816375752551257 7025167545612281814413443)
                  ·
                    refine ⟨10537751318418422721620165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7025167545612281814413443 10537751318418422721620165)
                    ·
                      refine ⟨1975828372203454260303781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10537751318418422721620165 1975828372203454260303781)
                      ·
                        rfl

theorem cell23_3847912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3847912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847912 prefixEnd_3847912 := by exact prefixLift 3847912
  have htrace : WordTrace (prefixWord ++ tailWord_3847912) baseStart_3847912 baseEnd_3847912 := by
    simpa [prefixWord, tailWord_3847912, baseEnd_3847912] using wordTrace_append hprefix tailTrace_3847912
  have hstable : (prefixWord ++ tailWord_3847912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847912).length < 2 ^ (prefixWord ++ tailWord_3847912).sum := by decide
  have hdescent : baseEnd_3847912 < baseStart_3847912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847915 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 3]
def baseStart_3847915 : Nat := 118140960795 + 3847915 * 2 ^ 59
def prefixEnd_3847915 : Nat := 4983230072969 + 3 ^ 40 * 3847915 * 2
def baseEnd_3847915 : Nat := 1975829912645417748566267

theorem tailTrace_3847915 : CollatzResearch.WordTrace tailWord_3847915 prefixEnd_3847915 1975829912645417748566267 := by
  unfold tailWord_3847915
  simp only [CollatzResearch.WordTrace]
  refine ⟨140344989854668601407009199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93563326569779067604672799 140344989854668601407009199)
  ·
    refine ⟨210517484782002902110513799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140344989854668601407009199 210517484782002902110513799)
    ·
      refine ⟨315776227173004353165770699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210517484782002902110513799 315776227173004353165770699)
      ·
        refine ⟨473664340759506529748656049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315776227173004353165770699 473664340759506529748656049)
        ·
          refine ⟨355248255569629897311492037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473664340759506529748656049 355248255569629897311492037)
          ·
            refine ⟨66609047919305605745904757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355248255569629897311492037 66609047919305605745904757)
            ·
              refine ⟨6244598242434900538678571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66609047919305605745904757 6244598242434900538678571)
              ·
                refine ⟨9366897363652350808017857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244598242434900538678571 9366897363652350808017857)
                ·
                  refine ⟨7025173022739263106013393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9366897363652350808017857 7025173022739263106013393)
                  ·
                    refine ⟨5268879767054447329510045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7025173022739263106013393 5268879767054447329510045)
                    ·
                      refine ⟨1975829912645417748566267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5268879767054447329510045 1975829912645417748566267)
                      ·
                        rfl

theorem cell23_3847915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 3].length) (baseStart_3847915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847915 prefixEnd_3847915 := by exact prefixLift 3847915
  have htrace : WordTrace (prefixWord ++ tailWord_3847915) baseStart_3847915 baseEnd_3847915 := by
    simpa [prefixWord, tailWord_3847915, baseEnd_3847915] using wordTrace_append hprefix tailTrace_3847915
  have hstable : (prefixWord ++ tailWord_3847915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847915).length < 2 ^ (prefixWord ++ tailWord_3847915).sum := by decide
  have hdescent : baseEnd_3847915 < baseStart_3847915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847918 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_3847918 : Nat := 118140960795 + 3847918 * 2 ^ 59
def prefixEnd_3847918 : Nat := 4983230072969 + 3 ^ 40 * 3847918 * 2
def baseEnd_3847918 : Nat := 219536828120820137425417

theorem tailTrace_3847918 : CollatzResearch.WordTrace tailWord_3847918 prefixEnd_3847918 219536828120820137425417 := by
  unfold tailWord_3847918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17543137409207216614921051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93563399515771821946245605 17543137409207216614921051)
  ·
    refine ⟨26314706113810824922381577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17543137409207216614921051 26314706113810824922381577)
    ·
      refine ⟨19736029585358118691786183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26314706113810824922381577 19736029585358118691786183)
      ·
        refine ⟨29604044378037178037679275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19736029585358118691786183 29604044378037178037679275)
        ·
          refine ⟨44406066567055767056518913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29604044378037178037679275 44406066567055767056518913)
          ·
            refine ⟨33304549925291825292389185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44406066567055767056518913 33304549925291825292389185)
            ·
              refine ⟨24978412443968868969291889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33304549925291825292389185 24978412443968868969291889)
              ·
                refine ⟨18733809332976651726968917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24978412443968868969291889 18733809332976651726968917)
                ·
                  refine ⟨219536828120820137425417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18733809332976651726968917 219536828120820137425417)
                  ·
                    rfl

theorem cell23_3847918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_3847918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847918 prefixEnd_3847918 := by exact prefixLift 3847918
  have htrace : WordTrace (prefixWord ++ tailWord_3847918) baseStart_3847918 baseEnd_3847918 := by
    simpa [prefixWord, tailWord_3847918, baseEnd_3847918] using wordTrace_append hprefix tailTrace_3847918
  have hstable : (prefixWord ++ tailWord_3847918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847918).length < 2 ^ (prefixWord ++ tailWord_3847918).sum := by decide
  have hdescent : baseEnd_3847918 < baseStart_3847918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847948 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_3847948 : Nat := 118140960795 + 3847948 * 2 ^ 59
def prefixEnd_3847948 : Nat := 4983230072969 + 3 ^ 40 * 3847948 * 2
def baseEnd_3847948 : Nat := 658615619169005373151205

theorem tailTrace_3847948 : CollatzResearch.WordTrace tailWord_3847948 prefixEnd_3847948 658615619169005373151205 := by
  unfold tailWord_3847948
  simp only [CollatzResearch.WordTrace]
  refine ⟨70173096731774524021480249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93564128975699365361973665 70173096731774524021480249)
  ·
    refine ⟨52629822548830893016110187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70173096731774524021480249 52629822548830893016110187)
    ·
      refine ⟨78944733823246339524165281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52629822548830893016110187 78944733823246339524165281)
      ·
        refine ⟨59208550367434754643123961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78944733823246339524165281 59208550367434754643123961)
        ·
          refine ⟨44406412775576065982342971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59208550367434754643123961 44406412775576065982342971)
          ·
            refine ⟨66609619163364098973514457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44406412775576065982342971 66609619163364098973514457)
            ·
              refine ⟨49957214372523074230135843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66609619163364098973514457 49957214372523074230135843)
              ·
                refine ⟨74935821558784611345203765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49957214372523074230135843 74935821558784611345203765)
                ·
                  refine ⟨7025233271136057313612853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74935821558784611345203765 7025233271136057313612853)
                  ·
                    refine ⟨658615619169005373151205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7025233271136057313612853 658615619169005373151205)
                    ·
                      rfl

theorem cell23_3847948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_3847948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847948 prefixEnd_3847948 := by exact prefixLift 3847948
  have htrace : WordTrace (prefixWord ++ tailWord_3847948) baseStart_3847948 baseEnd_3847948 := by
    simpa [prefixWord, tailWord_3847948, baseEnd_3847948] using wordTrace_append hprefix tailTrace_3847948
  have hstable : (prefixWord ++ tailWord_3847948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847948).length < 2 ^ (prefixWord ++ tailWord_3847948).sum := by decide
  have hdescent : baseEnd_3847948 < baseStart_3847948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847955 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 6, 3, 2]
def baseStart_3847955 : Nat := 118140960795 + 3847955 * 2 ^ 59
def prefixEnd_3847955 : Nat := 4983230072969 + 3 ^ 40 * 3847955 * 2
def baseEnd_3847955 : Nat := 1975850451871597592066083

theorem tailTrace_3847955 : CollatzResearch.WordTrace tailWord_3847955 prefixEnd_3847955 1975850451871597592066083 := by
  unfold tailWord_3847955
  simp only [CollatzResearch.WordTrace]
  refine ⟨140346448774523688238465319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93564299183015792158976879 140346448774523688238465319)
  ·
    refine ⟨210519673161785532357697979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140346448774523688238465319 210519673161785532357697979)
    ·
      refine ⟨315779509742678298536546969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210519673161785532357697979 315779509742678298536546969)
      ·
        refine ⟨236834632307008723902410227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315779509742678298536546969 236834632307008723902410227)
        ·
          refine ⟨355251948460513085853615341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236834632307008723902410227 355251948460513085853615341)
          ·
            refine ⟨133219480672692407195105753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355251948460513085853615341 133219480672692407195105753)
            ·
              refine ⟨99914610504519305396329315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133219480672692407195105753 99914610504519305396329315)
              ·
                refine ⟨149871915756778958094493973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99914610504519305396329315 149871915756778958094493973)
                ·
                  refine ⟨7025246051099013660679405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149871915756778958094493973 7025246051099013660679405)
                  ·
                    refine ⟨2634467269162130122754777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7025246051099013660679405 2634467269162130122754777)
                    ·
                      refine ⟨1975850451871597592066083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634467269162130122754777 1975850451871597592066083)
                      ·
                        rfl

theorem cell23_3847955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 3, 2].length) (baseStart_3847955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847955 prefixEnd_3847955 := by exact prefixLift 3847955
  have htrace : WordTrace (prefixWord ++ tailWord_3847955) baseStart_3847955 baseEnd_3847955 := by
    simpa [prefixWord, tailWord_3847955, baseEnd_3847955] using wordTrace_append hprefix tailTrace_3847955
  have hstable : (prefixWord ++ tailWord_3847955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847955).length < 2 ^ (prefixWord ++ tailWord_3847955).sum := by decide
  have hdescent : baseEnd_3847955 < baseStart_3847955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847962 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3]
def baseStart_3847962 : Nat := 118140960795 + 3847962 * 2 ^ 59
def prefixEnd_3847962 : Nat := 4983230072969 + 3 ^ 40 * 3847962 * 2
def baseEnd_3847962 : Nat := 1975854046236179064678551

theorem tailTrace_3847962 : CollatzResearch.WordTrace tailWord_3847962 prefixEnd_3847962 1975854046236179064678551 := by
  unfold tailWord_3847962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35086676021374582108492535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93564469390332218955980093 35086676021374582108492535)
  ·
    refine ⟨52630014032061873162738803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35086676021374582108492535 52630014032061873162738803)
    ·
      refine ⟨78945021048092809744108205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52630014032061873162738803 78945021048092809744108205)
      ·
        refine ⟨29604382893034803654040577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78945021048092809744108205 29604382893034803654040577)
        ·
          refine ⟨22203287169776102740530433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29604382893034803654040577 22203287169776102740530433)
          ·
            refine ⟨16652465377332077055397825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22203287169776102740530433 16652465377332077055397825)
            ·
              refine ⟨12489349032999057791548369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16652465377332077055397825 12489349032999057791548369)
              ·
                refine ⟨9367011774749293343661277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12489349032999057791548369 9367011774749293343661277)
                ·
                  refine ⟨3512629415530985003872979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9367011774749293343661277 3512629415530985003872979)
                  ·
                    refine ⟨5268944123296477505809469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3512629415530985003872979 5268944123296477505809469)
                    ·
                      refine ⟨1975854046236179064678551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5268944123296477505809469 1975854046236179064678551)
                      ·
                        rfl

theorem cell23_3847962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_3847962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847962 prefixEnd_3847962 := by exact prefixLift 3847962
  have htrace : WordTrace (prefixWord ++ tailWord_3847962) baseStart_3847962 baseEnd_3847962 := by
    simpa [prefixWord, tailWord_3847962, baseEnd_3847962] using wordTrace_append hprefix tailTrace_3847962
  have hstable : (prefixWord ++ tailWord_3847962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847962).length < 2 ^ (prefixWord ++ tailWord_3847962).sum := by decide
  have hdescent : baseEnd_3847962 < baseStart_3847962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847972 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_3847972 : Nat := 118140960795 + 3847972 * 2 ^ 59
def prefixEnd_3847972 : Nat := 4983230072969 + 3 ^ 40 * 3847972 * 2
def baseEnd_3847972 : Nat := 1975859181042724025553505

theorem tailTrace_3847972 : CollatzResearch.WordTrace tailWord_3847972 prefixEnd_3847972 1975859181042724025553505 := by
  unfold tailWord_3847972
  simp only [CollatzResearch.WordTrace]
  refine ⟨70173534407731050070917085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93564712543641400094556113 70173534407731050070917085)
  ·
    refine ⟨26315075402899143776593907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70173534407731050070917085 26315075402899143776593907)
    ·
      refine ⟨39472613104348715664890861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26315075402899143776593907 39472613104348715664890861)
      ·
        refine ⟨14802229914130768374334073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39472613104348715664890861 14802229914130768374334073)
        ·
          refine ⟨11101672435598076280750555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14802229914130768374334073 11101672435598076280750555)
          ·
            refine ⟨16652508653397114421125833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11101672435598076280750555 16652508653397114421125833)
            ·
              refine ⟨12489381490047835815844375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16652508653397114421125833 12489381490047835815844375)
              ·
                refine ⟨18734072235071753723766563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489381490047835815844375 18734072235071753723766563)
                ·
                  refine ⟨28101108352607630585649845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18734072235071753723766563 28101108352607630585649845)
                  ·
                    refine ⟨2634478908056965367404673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28101108352607630585649845 2634478908056965367404673)
                    ·
                      refine ⟨1975859181042724025553505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634478908056965367404673 1975859181042724025553505)
                      ·
                        rfl

theorem cell23_3847972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_3847972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847972 prefixEnd_3847972 := by exact prefixLift 3847972
  have htrace : WordTrace (prefixWord ++ tailWord_3847972) baseStart_3847972 baseEnd_3847972 := by
    simpa [prefixWord, tailWord_3847972, baseEnd_3847972] using wordTrace_append hprefix tailTrace_3847972
  have hstable : (prefixWord ++ tailWord_3847972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847972).length < 2 ^ (prefixWord ++ tailWord_3847972).sum := by decide
  have hdescent : baseEnd_3847972 < baseStart_3847972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3847989 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_3847989 : Nat := 118140960795 + 3847989 * 2 ^ 59
def prefixEnd_3847989 : Nat := 4983230072969 + 3 ^ 40 * 3847989 * 2
def baseEnd_3847989 : Nat := 1975867910213850459040927

theorem tailTrace_3847989 : CollatzResearch.WordTrace tailWord_3847989 prefixEnd_3847989 1975867910213850459040927 := by
  unfold tailWord_3847989
  simp only [CollatzResearch.WordTrace]
  refine ⟨140347688856400512045203021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93565125904267008030135347 140347688856400512045203021)
  ·
    refine ⟨52630383321150192016951133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140347688856400512045203021 52630383321150192016951133)
    ·
      refine ⟨19736393745431322006356675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52630383321150192016951133 19736393745431322006356675)
      ·
        refine ⟨29604590618146983009535013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19736393745431322006356675 29604590618146983009535013)
        ·
          refine ⟨5550860740902559314287815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29604590618146983009535013 5550860740902559314287815)
          ·
            refine ⟨8326291111353838971431723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550860740902559314287815 8326291111353838971431723)
            ·
              refine ⟨12489436667030758457147585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8326291111353838971431723 12489436667030758457147585)
              ·
                refine ⟨9367077500273068842860689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12489436667030758457147585 9367077500273068842860689)
                ·
                  refine ⟨7025308125204801632145517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9367077500273068842860689 7025308125204801632145517)
                  ·
                    refine ⟨2634490546951800612054569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7025308125204801632145517 2634490546951800612054569)
                    ·
                      refine ⟨1975867910213850459040927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634490546951800612054569 1975867910213850459040927)
                      ·
                        rfl

theorem cell23_3847989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_3847989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3847989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3847989 prefixEnd_3847989 := by exact prefixLift 3847989
  have htrace : WordTrace (prefixWord ++ tailWord_3847989) baseStart_3847989 baseEnd_3847989 := by
    simpa [prefixWord, tailWord_3847989, baseEnd_3847989] using wordTrace_append hprefix tailTrace_3847989
  have hstable : (prefixWord ++ tailWord_3847989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3847989).length < 2 ^ (prefixWord ++ tailWord_3847989).sum := by decide
  have hdescent : baseEnd_3847989 < baseStart_3847989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3847989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848005 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_3848005 : Nat := 118140960795 + 3848005 * 2 ^ 59
def prefixEnd_3848005 : Nat := 4983230072969 + 3 ^ 40 * 3848005 * 2
def baseEnd_3848005 : Nat := 1975876125904322396440853

theorem tailTrace_3848005 : CollatzResearch.WordTrace tailWord_3848005 prefixEnd_3848005 1975876125904322396440853 := by
  unfold tailWord_3848005
  simp only [CollatzResearch.WordTrace]
  refine ⟨140348272424342546777785469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93565514949561697851856979 140348272424342546777785469)
  ·
    refine ⟨52630602159128455041669551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140348272424342546777785469 52630602159128455041669551)
    ·
      refine ⟨78945903238692682562504327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52630602159128455041669551 78945903238692682562504327)
      ·
        refine ⟨118418854858039023843756491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78945903238692682562504327 118418854858039023843756491)
        ·
          refine ⟨177628282287058535765634737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118418854858039023843756491 177628282287058535765634737)
          ·
            refine ⟨133221211715293901824226053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177628282287058535765634737 133221211715293901824226053)
            ·
              refine ⟨24978977196617606592042385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133221211715293901824226053 24978977196617606592042385)
              ·
                refine ⟨18734232897463204944031789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24978977196617606592042385 18734232897463204944031789)
                ·
                  refine ⟨7025337336548701854011921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18734232897463204944031789 7025337336548701854011921)
                  ·
                    refine ⟨5269003002411526390508941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7025337336548701854011921 5269003002411526390508941)
                    ·
                      refine ⟨1975876125904322396440853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5269003002411526390508941 1975876125904322396440853)
                      ·
                        rfl

theorem cell23_3848005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_3848005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848005 prefixEnd_3848005 := by exact prefixLift 3848005
  have htrace : WordTrace (prefixWord ++ tailWord_3848005) baseStart_3848005 baseEnd_3848005 := by
    simpa [prefixWord, tailWord_3848005, baseEnd_3848005] using wordTrace_append hprefix tailTrace_3848005
  have hstable : (prefixWord ++ tailWord_3848005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848005).length < 2 ^ (prefixWord ++ tailWord_3848005).sum := by decide
  have hdescent : baseEnd_3848005 < baseStart_3848005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848008 : List Nat := [2, 1, 3, 1, 1, 4, 1, 10]
def baseStart_3848008 : Nat := 118140960795 + 3848008 * 2 ^ 59
def prefixEnd_3848008 : Nat := 4983230072969 + 3 ^ 40 * 3848008 * 2
def baseEnd_3848008 : Nat := 73180654309121699433457

theorem tailTrace_3848008 : CollatzResearch.WordTrace tailWord_3848008 prefixEnd_3848008 73180654309121699433457 := by
  unfold tailWord_3848008
  simp only [CollatzResearch.WordTrace]
  refine ⟨70174190921665839145072339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93565587895554452193429785 70174190921665839145072339)
  ·
    refine ⟨105261286382498758717608509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70174190921665839145072339 105261286382498758717608509)
    ·
      refine ⟨39472982393437034519103191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105261286382498758717608509 39472982393437034519103191)
      ·
        refine ⟨59209473590155551778654787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39472982393437034519103191 59209473590155551778654787)
        ·
          refine ⟨88814210385233327667982181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59209473590155551778654787 88814210385233327667982181)
          ·
            refine ⟨16652664447231248937746659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88814210385233327667982181 16652664447231248937746659)
            ·
              refine ⟨24978996670846873406619989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16652664447231248937746659 24978996670846873406619989)
              ·
                refine ⟨73180654309121699433457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24978996670846873406619989 73180654309121699433457)
                ·
                  rfl

theorem cell23_3848008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 10].length) (baseStart_3848008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848008 prefixEnd_3848008 := by exact prefixLift 3848008
  have htrace : WordTrace (prefixWord ++ tailWord_3848008) baseStart_3848008 baseEnd_3848008 := by
    simpa [prefixWord, tailWord_3848008, baseEnd_3848008] using wordTrace_append hprefix tailTrace_3848008
  have hstable : (prefixWord ++ tailWord_3848008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848008).length < 2 ^ (prefixWord ++ tailWord_3848008).sum := by decide
  have hdescent : baseEnd_3848008 < baseStart_3848008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848039 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_3848039 : Nat := 118140960795 + 3848039 * 2 ^ 59
def prefixEnd_3848039 : Nat := 4983230072969 + 3 ^ 40 * 3848039 * 2
def baseEnd_3848039 : Nat := 1975893584246575263415697

theorem tailTrace_3848039 : CollatzResearch.WordTrace tailWord_3848039 prefixEnd_3848039 1975893584246575263415697 := by
  unfold tailWord_3848039
  simp only [CollatzResearch.WordTrace]
  refine ⟨140349512506219370584523171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93566341670812913723015447 140349512506219370584523171)
  ·
    refine ⟨210524268759329055876784757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140349512506219370584523171 210524268759329055876784757)
    ·
      refine ⟨19736650196187098988448571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210524268759329055876784757 19736650196187098988448571)
      ·
        refine ⟨29604975294280648482672857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19736650196187098988448571 29604975294280648482672857)
        ·
          refine ⟨22203731470710486362004643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29604975294280648482672857 22203731470710486362004643)
          ·
            refine ⟨33305597206065729543006965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22203731470710486362004643 33305597206065729543006965)
            ·
              refine ⟨3122399738068662144656903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33305597206065729543006965 3122399738068662144656903)
              ·
                refine ⟨4683599607102993216985355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122399738068662144656903 4683599607102993216985355)
                ·
                  refine ⟨7025399410654489825478033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683599607102993216985355 7025399410654489825478033)
                  ·
                    refine ⟨5269049557990867369108525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7025399410654489825478033 5269049557990867369108525)
                    ·
                      refine ⟨1975893584246575263415697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5269049557990867369108525 1975893584246575263415697)
                      ·
                        rfl

theorem cell23_3848039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_3848039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848039 prefixEnd_3848039 := by exact prefixLift 3848039
  have htrace : WordTrace (prefixWord ++ tailWord_3848039) baseStart_3848039 baseEnd_3848039 := by
    simpa [prefixWord, tailWord_3848039, baseEnd_3848039] using wordTrace_append hprefix tailTrace_3848039
  have hstable : (prefixWord ++ tailWord_3848039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848039).length < 2 ^ (prefixWord ++ tailWord_3848039).sum := by decide
  have hdescent : baseEnd_3848039 < baseStart_3848039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848042 : List Nat := [3, 1, 3, 4, 2, 10]
def baseStart_3848042 : Nat := 118140960795 + 3848042 * 2 ^ 59
def prefixEnd_3848042 : Nat := 4983230072969 + 3 ^ 40 * 3848042 * 2
def baseEnd_3848042 : Nat := 8131255657154480459581

theorem tailTrace_3848042 : CollatzResearch.WordTrace tailWord_3848042 prefixEnd_3848042 8131255657154480459581 := by
  unfold tailWord_3848042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35087405481302125524220595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93566414616805668064588253 35087405481302125524220595)
  ·
    refine ⟨52631108221953188286330893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35087405481302125524220595 52631108221953188286330893)
    ·
      refine ⟨19736665583232445607374085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52631108221953188286330893 19736665583232445607374085)
      ·
        refine ⟨3700624796856083551382641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19736665583232445607374085 3700624796856083551382641)
        ·
          refine ⟨2775468597642062663536981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3700624796856083551382641 2775468597642062663536981)
          ·
            refine ⟨8131255657154480459581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2775468597642062663536981 8131255657154480459581)
            ·
              rfl

theorem cell23_3848042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 10].length) (baseStart_3848042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848042 prefixEnd_3848042 := by exact prefixLift 3848042
  have htrace : WordTrace (prefixWord ++ tailWord_3848042) baseStart_3848042 baseEnd_3848042 := by
    simpa [prefixWord, tailWord_3848042, baseEnd_3848042] using wordTrace_append hprefix tailTrace_3848042
  have hstable : (prefixWord ++ tailWord_3848042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848042).length < 2 ^ (prefixWord ++ tailWord_3848042).sum := by decide
  have hdescent : baseEnd_3848042 < baseStart_3848042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848115 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 7]
def baseStart_3848115 : Nat := 118140960795 + 3848115 * 2 ^ 59
def prefixEnd_3848115 : Nat := 4983230072969 + 3 ^ 40 * 3848115 * 2
def baseEnd_3848115 : Nat := 219548067641812996229483

theorem tailTrace_3848115 : CollatzResearch.WordTrace tailWord_3848115 prefixEnd_3848115 219548067641812996229483 := by
  unfold tailWord_3848115
  simp only [CollatzResearch.WordTrace]
  refine ⟨140352284453944035564289799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93568189635962690376193199 140352284453944035564289799)
  ·
    refine ⟨210528426680916053346434699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140352284453944035564289799 210528426680916053346434699)
    ·
      refine ⟨315792640021374080019652049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210528426680916053346434699 315792640021374080019652049)
      ·
        refine ⟨236844480016030560014739037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315792640021374080019652049 236844480016030560014739037)
        ·
          refine ⟨88816680006011460005527139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236844480016030560014739037 88816680006011460005527139)
          ·
            refine ⟨133225020009017190008290709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88816680006011460005527139 133225020009017190008290709)
            ·
              refine ⟨6244922812922680781638627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133225020009017190008290709 6244922812922680781638627)
              ·
                refine ⟨9367384219384021172457941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244922812922680781638627 9367384219384021172457941)
                ·
                  refine ⟨219548067641812996229483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9367384219384021172457941 219548067641812996229483)
                  ·
                    rfl

theorem cell23_3848115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 7].length) (baseStart_3848115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848115 prefixEnd_3848115 := by exact prefixLift 3848115
  have htrace : WordTrace (prefixWord ++ tailWord_3848115) baseStart_3848115 baseEnd_3848115 := by
    simpa [prefixWord, tailWord_3848115, baseEnd_3848115] using wordTrace_append hprefix tailTrace_3848115
  have hstable : (prefixWord ++ tailWord_3848115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848115).length < 2 ^ (prefixWord ++ tailWord_3848115).sum := by decide
  have hdescent : baseEnd_3848115 < baseStart_3848115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848126 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_3848126 : Nat := 118140960795 + 3848126 * 2 ^ 59
def prefixEnd_3848126 : Nat := 4983230072969 + 3 ^ 40 * 3848126 * 2
def baseEnd_3848126 : Nat := 1975938257063516423027797

theorem tailTrace_3848126 : CollatzResearch.WordTrace tailWord_3848126 prefixEnd_3848126 1975938257063516423027797 := by
  unfold tailWord_3848126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17544085707113023055367529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93568457104602789628626821 17544085707113023055367529)
  ·
    refine ⟨13158064280334767291525647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17544085707113023055367529 13158064280334767291525647)
    ·
      refine ⟨19737096420502150937288471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13158064280334767291525647 19737096420502150937288471)
      ·
        refine ⟨29605644630753226405932707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19737096420502150937288471 29605644630753226405932707)
        ·
          refine ⟨44408466946129839608899061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29605644630753226405932707 44408466946129839608899061)
          ·
            refine ⟨4163293776199672463334287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44408466946129839608899061 4163293776199672463334287)
            ·
              refine ⟨6244940664299508695001431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163293776199672463334287 6244940664299508695001431)
              ·
                refine ⟨9367410996449263042502147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244940664299508695001431 9367410996449263042502147)
                ·
                  refine ⟨14051116494673894563753221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9367410996449263042502147 14051116494673894563753221)
                  ·
                    refine ⟨2634584342751355230703729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14051116494673894563753221 2634584342751355230703729)
                    ·
                      refine ⟨1975938257063516423027797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634584342751355230703729 1975938257063516423027797)
                      ·
                        rfl

theorem cell23_3848126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_3848126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848126 prefixEnd_3848126 := by exact prefixLift 3848126
  have htrace : WordTrace (prefixWord ++ tailWord_3848126) baseStart_3848126 baseEnd_3848126 := by
    simpa [prefixWord, tailWord_3848126, baseEnd_3848126] using wordTrace_append hprefix tailTrace_3848126
  have hstable : (prefixWord ++ tailWord_3848126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848126).length < 2 ^ (prefixWord ++ tailWord_3848126).sum := by decide
  have hdescent : baseEnd_3848126 < baseStart_3848126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848149 : List Nat := [1, 3, 2, 3, 2, 1, 3, 3, 5]
def baseStart_3848149 : Nat := 118140960795 + 3848149 * 2 ^ 59
def prefixEnd_3848149 : Nat := 4983230072969 + 3 ^ 40 * 3848149 * 2
def baseEnd_3848149 : Nat := 219550007457618870337799

theorem tailTrace_3848149 : CollatzResearch.WordTrace tailWord_3848149 prefixEnd_3848149 219550007457618870337799 := by
  unfold tailWord_3848149
  simp only [CollatzResearch.WordTrace]
  refine ⟨140353524535820859371027501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93569016357213906247351667 140353524535820859371027501)
  ·
    refine ⟨52632571700932822264135313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140353524535820859371027501 52632571700932822264135313)
    ·
      refine ⟨39474428775699616698101485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52632571700932822264135313 39474428775699616698101485)
      ·
        refine ⟨14802910790887356261788057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39474428775699616698101485 14802910790887356261788057)
        ·
          refine ⟨11102183093165517196341043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14802910790887356261788057 11102183093165517196341043)
          ·
            refine ⟨16653274639748275794511565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11102183093165517196341043 16653274639748275794511565)
            ·
              refine ⟨6244977989905603422941837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16653274639748275794511565 6244977989905603422941837)
              ·
                refine ⟨2341866746214601283603189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6244977989905603422941837 2341866746214601283603189)
                ·
                  refine ⟨219550007457618870337799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2341866746214601283603189 219550007457618870337799)
                  ·
                    rfl

theorem cell23_3848149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_3848149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848149 prefixEnd_3848149 := by exact prefixLift 3848149
  have htrace : WordTrace (prefixWord ++ tailWord_3848149) baseStart_3848149 baseEnd_3848149 := by
    simpa [prefixWord, tailWord_3848149, baseEnd_3848149] using wordTrace_append hprefix tailTrace_3848149
  have hstable : (prefixWord ++ tailWord_3848149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848149).length < 2 ^ (prefixWord ++ tailWord_3848149).sum := by decide
  have hdescent : baseEnd_3848149 < baseStart_3848149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848195 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 4]
def baseStart_3848195 : Nat := 118140960795 + 3848195 * 2 ^ 59
def prefixEnd_3848195 : Nat := 4983230072969 + 3 ^ 40 * 3848195 * 2
def baseEnd_3848195 : Nat := 1975973687228676653064979

theorem tailTrace_3848195 : CollatzResearch.WordTrace tailWord_3848195 prefixEnd_3848195 1975973687228676653064979 := by
  unfold tailWord_3848195
  simp only [CollatzResearch.WordTrace]
  refine ⟨140355202293654209227202039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93570134862436139484801359 140355202293654209227202039)
  ·
    refine ⟨210532803440481313840803059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140355202293654209227202039 210532803440481313840803059)
    ·
      refine ⟨315799205160721970761204589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210532803440481313840803059 315799205160721970761204589)
      ·
        refine ⟨118424701935270739035451721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315799205160721970761204589 118424701935270739035451721)
        ·
          refine ⟨88818526451453054276588791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118424701935270739035451721 88818526451453054276588791)
          ·
            refine ⟨133227789677179581414883187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88818526451453054276588791 133227789677179581414883187)
            ·
              refine ⟨199841684515769372122324781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133227789677179581414883187 199841684515769372122324781)
              ·
                refine ⟨74940631693413514545871793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199841684515769372122324781 74940631693413514545871793)
                ·
                  refine ⟨56205473770060135909403845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74940631693413514545871793 56205473770060135909403845)
                  ·
                    refine ⟨10538526331886275483013221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56205473770060135909403845 10538526331886275483013221)
                    ·
                      refine ⟨1975973687228676653064979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10538526331886275483013221 1975973687228676653064979)
                      ·
                        rfl

theorem cell23_3848195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_3848195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848195 prefixEnd_3848195 := by exact prefixLift 3848195
  have htrace : WordTrace (prefixWord ++ tailWord_3848195) baseStart_3848195 baseEnd_3848195 := by
    simpa [prefixWord, tailWord_3848195, baseEnd_3848195] using wordTrace_append hprefix tailTrace_3848195
  have hstable : (prefixWord ++ tailWord_3848195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848195).length < 2 ^ (prefixWord ++ tailWord_3848195).sum := by decide
  have hdescent : baseEnd_3848195 < baseStart_3848195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848196 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_3848196 : Nat := 118140960795 + 3848196 * 2 ^ 59
def prefixEnd_3848196 : Nat := 4983230072969 + 3 ^ 40 * 3848196 * 2
def baseEnd_3848196 : Nat := 658658066903110383050825

theorem tailTrace_3848196 : CollatzResearch.WordTrace tailWord_3848196 prefixEnd_3848196 658658066903110383050825 := by
  unfold tailWord_3848196
  simp only [CollatzResearch.WordTrace]
  refine ⟨70177619383325293198994221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93570159177767057598658961 70177619383325293198994221)
  ·
    refine ⟨26316607268746984949622833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70177619383325293198994221 26316607268746984949622833)
    ·
      refine ⟨19737455451560238712217125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26316607268746984949622833 19737455451560238712217125)
      ·
        refine ⟨3700772897167544758540711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19737455451560238712217125 3700772897167544758540711)
        ·
          refine ⟨5551159345751317137811067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700772897167544758540711 5551159345751317137811067)
          ·
            refine ⟨8326739018626975706716601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551159345751317137811067 8326739018626975706716601)
            ·
              refine ⟨6245054263970231780037451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8326739018626975706716601 6245054263970231780037451)
              ·
                refine ⟨9367581395955347670056177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245054263970231780037451 9367581395955347670056177)
                ·
                  refine ⟨7025686046966510752542133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9367581395955347670056177 7025686046966510752542133)
                  ·
                    refine ⟨658658066903110383050825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7025686046966510752542133 658658066903110383050825)
                    ·
                      rfl

theorem cell23_3848196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_3848196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848196 prefixEnd_3848196 := by exact prefixLift 3848196
  have htrace : WordTrace (prefixWord ++ tailWord_3848196) baseStart_3848196 baseEnd_3848196 := by
    simpa [prefixWord, tailWord_3848196, baseEnd_3848196] using wordTrace_append hprefix tailTrace_3848196
  have hstable : (prefixWord ++ tailWord_3848196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848196).length < 2 ^ (prefixWord ++ tailWord_3848196).sum := by decide
  have hdescent : baseEnd_3848196 < baseStart_3848196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848199 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3848199 : Nat := 118140960795 + 3848199 * 2 ^ 59
def prefixEnd_3848199 : Nat := 4983230072969 + 3 ^ 40 * 3848199 * 2
def baseEnd_3848199 : Nat := 1975975741151294637414961

theorem tailTrace_3848199 : CollatzResearch.WordTrace tailWord_3848199 prefixEnd_3848199 1975975741151294637414961 := by
  unfold tailWord_3848199
  simp only [CollatzResearch.WordTrace]
  refine ⟨140355348185639717910347651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93570232123759811940231767 140355348185639717910347651)
  ·
    refine ⟨210533022278459576865521477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140355348185639717910347651 210533022278459576865521477)
    ·
      refine ⟨39474941677211170662285277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210533022278459576865521477 39474941677211170662285277)
      ·
        refine ⟨14803103128954188998356979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39474941677211170662285277 14803103128954188998356979)
        ·
          refine ⟨22204654693431283497535469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14803103128954188998356979 22204654693431283497535469)
          ·
            refine ⟨8326745510036731311575801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22204654693431283497535469 8326745510036731311575801)
            ·
              refine ⟨6245059132527548483681851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8326745510036731311575801 6245059132527548483681851)
              ·
                refine ⟨9367588698791322725522777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245059132527548483681851 9367588698791322725522777)
                ·
                  refine ⟨7025691524093492044142083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9367588698791322725522777 7025691524093492044142083)
                  ·
                    refine ⟨10538537286140238066213125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7025691524093492044142083 10538537286140238066213125)
                    ·
                      refine ⟨1975975741151294637414961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10538537286140238066213125 1975975741151294637414961)
                      ·
                        rfl

theorem cell23_3848199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3848199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848199 prefixEnd_3848199 := by exact prefixLift 3848199
  have htrace : WordTrace (prefixWord ++ tailWord_3848199) baseStart_3848199 baseEnd_3848199 := by
    simpa [prefixWord, tailWord_3848199, baseEnd_3848199] using wordTrace_append hprefix tailTrace_3848199
  have hstable : (prefixWord ++ tailWord_3848199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848199).length < 2 ^ (prefixWord ++ tailWord_3848199).sum := by decide
  have hdescent : baseEnd_3848199 < baseStart_3848199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848226 : List Nat := [3, 3, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_3848226 : Nat := 118140960795 + 3848226 * 2 ^ 59
def prefixEnd_3848226 : Nat := 4983230072969 + 3 ^ 40 * 3848226 * 2
def baseEnd_3848226 : Nat := 658663201709655343925779

theorem tailTrace_3848226 : CollatzResearch.WordTrace tailWord_3848226 prefixEnd_3848226 658663201709655343925779 := by
  unfold tailWord_3848226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35089083239135475380395133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93570888637694601014387021 35089083239135475380395133)
  ·
    refine ⟨13158406214675803267648175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35089083239135475380395133 13158406214675803267648175)
    ·
      refine ⟨19737609322013704901472263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13158406214675803267648175 19737609322013704901472263)
      ·
        refine ⟨29606413983020557352208395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19737609322013704901472263 29606413983020557352208395)
        ·
          refine ⟨44409620974530836028312593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29606413983020557352208395 44409620974530836028312593)
          ·
            refine ⟨33307215730898127021234445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44409620974530836028312593 33307215730898127021234445)
            ·
              refine ⟨12490205899086797632962917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33307215730898127021234445 12490205899086797632962917)
              ·
                refine ⟨2341913606078774556180547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12490205899086797632962917 2341913606078774556180547)
                ·
                  refine ⟨3512870409118161834270821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2341913606078774556180547 3512870409118161834270821)
                  ·
                    refine ⟨658663201709655343925779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3512870409118161834270821 658663201709655343925779)
                    ·
                      rfl

theorem cell23_3848226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_3848226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848226 prefixEnd_3848226 := by exact prefixLift 3848226
  have htrace : WordTrace (prefixWord ++ tailWord_3848226) baseStart_3848226 baseEnd_3848226 := by
    simpa [prefixWord, tailWord_3848226, baseEnd_3848226] using wordTrace_append hprefix tailTrace_3848226
  have hstable : (prefixWord ++ tailWord_3848226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848226).length < 2 ^ (prefixWord ++ tailWord_3848226).sum := by decide
  have hdescent : baseEnd_3848226 < baseStart_3848226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848252 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_3848252 : Nat := 118140960795 + 3848252 * 2 ^ 59
def prefixEnd_3848252 : Nat := 4983230072969 + 3 ^ 40 * 3848252 * 2
def baseEnd_3848252 : Nat := 658667651875327643350739

theorem tailTrace_3848252 : CollatzResearch.WordTrace tailWord_3848252 prefixEnd_3848252 658667651875327643350739 := by
  unfold tailWord_3848252
  simp only [CollatzResearch.WordTrace]
  refine ⟨70178640627223853981013505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93571520836298471974684673 70178640627223853981013505)
  ·
    refine ⟨52633980470417890485760129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70178640627223853981013505 52633980470417890485760129)
    ·
      refine ⟨39475485352813417864320097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52633980470417890485760129 39475485352813417864320097)
      ·
        refine ⟨29606614014610063398240073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39475485352813417864320097 29606614014610063398240073)
        ·
          refine ⟨22204960510957547548680055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29606614014610063398240073 22204960510957547548680055)
          ·
            refine ⟨33307440766436321323020083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22204960510957547548680055 33307440766436321323020083)
            ·
              refine ⟨49961161149654481984530125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33307440766436321323020083 49961161149654481984530125)
              ·
                refine ⟨18735435431120430744198797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49961161149654481984530125 18735435431120430744198797)
                ·
                  refine ⟨7025788286670161529074549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18735435431120430744198797 7025788286670161529074549)
                  ·
                    refine ⟨658667651875327643350739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7025788286670161529074549 658667651875327643350739)
                    ·
                      rfl

theorem cell23_3848252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_3848252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848252 prefixEnd_3848252 := by exact prefixLift 3848252
  have htrace : WordTrace (prefixWord ++ tailWord_3848252) baseStart_3848252 baseEnd_3848252 := by
    simpa [prefixWord, tailWord_3848252, baseEnd_3848252] using wordTrace_append hprefix tailTrace_3848252
  have hstable : (prefixWord ++ tailWord_3848252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848252).length < 2 ^ (prefixWord ++ tailWord_3848252).sum := by decide
  have hdescent : baseEnd_3848252 < baseStart_3848252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848259 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 2, 3, 2]
def baseStart_3848259 : Nat := 118140960795 + 3848259 * 2 ^ 59
def prefixEnd_3848259 : Nat := 4983230072969 + 3 ^ 40 * 3848259 * 2
def baseEnd_3848259 : Nat := 1976006549990564402664685

theorem tailTrace_3848259 : CollatzResearch.WordTrace tailWord_3848259 prefixEnd_3848259 1976006549990564402664685 := by
  unfold tailWord_3848259
  simp only [CollatzResearch.WordTrace]
  refine ⟨140357536565422348157531831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93571691043614898771687887 140357536565422348157531831)
  ·
    refine ⟨210536304848133522236297747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140357536565422348157531831 210536304848133522236297747)
    ·
      refine ⟨315804457272200283354446621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210536304848133522236297747 315804457272200283354446621)
      ·
        refine ⟨118426671477075106257917483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315804457272200283354446621 118426671477075106257917483)
        ·
          refine ⟨177640007215612659386876225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118426671477075106257917483 177640007215612659386876225)
          ·
            refine ⟨133230005411709494540157169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177640007215612659386876225 133230005411709494540157169)
            ·
              refine ⟨99922504058782120905117877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133230005411709494540157169 99922504058782120905117877)
              ·
                refine ⟨9367734755510823834854801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99922504058782120905117877 9367734755510823834854801)
                ·
                  refine ⟨7025801066633117876141101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9367734755510823834854801 7025801066633117876141101)
                  ·
                    refine ⟨2634675399987419203552913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7025801066633117876141101 2634675399987419203552913)
                    ·
                      refine ⟨1976006549990564402664685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634675399987419203552913 1976006549990564402664685)
                      ·
                        rfl

theorem cell23_3848259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_3848259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848259 prefixEnd_3848259 := by exact prefixLift 3848259
  have htrace : WordTrace (prefixWord ++ tailWord_3848259) baseStart_3848259 baseEnd_3848259 := by
    simpa [prefixWord, tailWord_3848259, baseEnd_3848259] using wordTrace_append hprefix tailTrace_3848259
  have hstable : (prefixWord ++ tailWord_3848259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848259).length < 2 ^ (prefixWord ++ tailWord_3848259).sum := by decide
  have hdescent : baseEnd_3848259 < baseStart_3848259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848292 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3848292 : Nat := 118140960795 + 3848292 * 2 ^ 59
def prefixEnd_3848292 : Nat := 4983230072969 + 3 ^ 40 * 3848292 * 2
def baseEnd_3848292 : Nat := 1976023494852162773552033

theorem tailTrace_3848292 : CollatzResearch.WordTrace tailWord_3848292 prefixEnd_3848292 1976023494852162773552033 := by
  unfold tailWord_3848292
  simp only [CollatzResearch.WordTrace]
  refine ⟨70179370087151397396741565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93572493449535196528988753 70179370087151397396741565)
  ·
    refine ⟨26317263782681774023778087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70179370087151397396741565 26317263782681774023778087)
    ·
      refine ⟨39475895674022661035667131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26317263782681774023778087 39475895674022661035667131)
      ·
        refine ⟨59213843511033991553500697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39475895674022661035667131 59213843511033991553500697)
        ·
          refine ⟨44410382633275493665125523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59213843511033991553500697 44410382633275493665125523)
          ·
            refine ⟨66615573949913240497688285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44410382633275493665125523 66615573949913240497688285)
            ·
              refine ⟨24980840231217465186633107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66615573949913240497688285 24980840231217465186633107)
              ·
                refine ⟨37471260346826197779949661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24980840231217465186633107 37471260346826197779949661)
                ·
                  refine ⟨14051722630059824167481123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37471260346826197779949661 14051722630059824167481123)
                  ·
                    refine ⟨21077583945089736251221685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14051722630059824167481123 21077583945089736251221685)
                    ·
                      refine ⟨1976023494852162773552033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21077583945089736251221685 1976023494852162773552033)
                      ·
                        rfl

theorem cell23_3848292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3848292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848292 prefixEnd_3848292 := by exact prefixLift 3848292
  have htrace : WordTrace (prefixWord ++ tailWord_3848292) baseStart_3848292 baseEnd_3848292 := by
    simpa [prefixWord, tailWord_3848292, baseEnd_3848292] using wordTrace_append hprefix tailTrace_3848292
  have hstable : (prefixWord ++ tailWord_3848292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848292).length < 2 ^ (prefixWord ++ tailWord_3848292).sum := by decide
  have hdescent : baseEnd_3848292 < baseStart_3848292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848306 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_3848306 : Nat := 118140960795 + 3848306 * 2 ^ 59
def prefixEnd_3848306 : Nat := 4983230072969 + 3 ^ 40 * 3848306 * 2
def baseEnd_3848306 : Nat := 1976030683581325718776969

theorem tailTrace_3848306 : CollatzResearch.WordTrace tailWord_3848306 prefixEnd_3848306 1976030683581325718776969 := by
  unfold tailWord_3848306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35089812699063018796123193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93572833864168050122995181 35089812699063018796123193)
  ·
    refine ⟨26317359524297264097092395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35089812699063018796123193 26317359524297264097092395)
    ·
      refine ⟨39476039286445896145638593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26317359524297264097092395 39476039286445896145638593)
      ·
        refine ⟨29607029464834422109228945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39476039286445896145638593 29607029464834422109228945)
        ·
          refine ⟨22205272098625816581921709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29607029464834422109228945 22205272098625816581921709)
          ·
            refine ⟨8326977036984681218220641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22205272098625816581921709 8326977036984681218220641)
            ·
              refine ⟨6245232777738510913665481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8326977036984681218220641 6245232777738510913665481)
              ·
                refine ⟨4683924583303883185249111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6245232777738510913665481 4683924583303883185249111)
                ·
                  refine ⟨7025886874955824777873667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683924583303883185249111 7025886874955824777873667)
                  ·
                    refine ⟨10538830312433737166810501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7025886874955824777873667 10538830312433737166810501)
                    ·
                      refine ⟨1976030683581325718776969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10538830312433737166810501 1976030683581325718776969)
                      ·
                        rfl

theorem cell23_3848306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_3848306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848306 prefixEnd_3848306 := by exact prefixLift 3848306
  have htrace : WordTrace (prefixWord ++ tailWord_3848306) baseStart_3848306 baseEnd_3848306 := by
    simpa [prefixWord, tailWord_3848306, baseEnd_3848306] using wordTrace_append hprefix tailTrace_3848306
  have hstable : (prefixWord ++ tailWord_3848306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848306).length < 2 ^ (prefixWord ++ tailWord_3848306).sum := by decide
  have hdescent : baseEnd_3848306 < baseStart_3848306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848373 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3848373 : Nat := 118140960795 + 3848373 * 2 ^ 59
def prefixEnd_3848373 : Nat := 4983230072969 + 3 ^ 40 * 3848373 * 2
def baseEnd_3848373 : Nat := 1976065086785176956639161

theorem tailTrace_3848373 : CollatzResearch.WordTrace tailWord_3848373 prefixEnd_3848373 1976065086785176956639161 := by
  unfold tailWord_3848373
  simp only [CollatzResearch.WordTrace]
  refine ⟨140361694487009345627181773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93574462991339563751454515 140361694487009345627181773)
  ·
    refine ⟨52635635432628504610193165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140361694487009345627181773 52635635432628504610193165)
    ·
      refine ⟨19738363287235689228822437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52635635432628504610193165 19738363287235689228822437)
      ·
        refine ⟨3700943116356691730404207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19738363287235689228822437 3700943116356691730404207)
        ·
          refine ⟨5551414674535037595606311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700943116356691730404207 5551414674535037595606311)
          ·
            refine ⟨8327122011802556393409467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551414674535037595606311 8327122011802556393409467)
            ·
              refine ⟨12490683017703834590114201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8327122011802556393409467 12490683017703834590114201)
              ·
                refine ⟨9368012263277875942585651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12490683017703834590114201 9368012263277875942585651)
                ·
                  refine ⟨14052018394916813913878477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9368012263277875942585651 14052018394916813913878477)
                  ·
                    refine ⟨5269506898093805217704429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14052018394916813913878477 5269506898093805217704429)
                    ·
                      refine ⟨1976065086785176956639161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5269506898093805217704429 1976065086785176956639161)
                      ·
                        rfl

theorem cell23_3848373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3848373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848373 prefixEnd_3848373 := by exact prefixLift 3848373
  have htrace : WordTrace (prefixWord ++ tailWord_3848373) baseStart_3848373 baseEnd_3848373 := by
    simpa [prefixWord, tailWord_3848373, baseEnd_3848373] using wordTrace_append hprefix tailTrace_3848373
  have hstable : (prefixWord ++ tailWord_3848373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848373).length < 2 ^ (prefixWord ++ tailWord_3848373).sum := by decide
  have hdescent : baseEnd_3848373 < baseStart_3848373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848392 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_3848392 : Nat := 118140960795 + 3848392 * 2 ^ 59
def prefixEnd_3848392 : Nat := 4983230072969 + 3 ^ 40 * 3848392 * 2
def baseEnd_3848392 : Nat := 1976074842917612382301573

theorem tailTrace_3848392 : CollatzResearch.WordTrace tailWord_3848392 prefixEnd_3848392 1976074842917612382301573 := by
  unfold tailWord_3848392
  simp only [CollatzResearch.WordTrace]
  refine ⟨70181193736970255936061715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93574924982627007914748953 70181193736970255936061715)
  ·
    refine ⟨105271790605455383904092573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70181193736970255936061715 105271790605455383904092573)
    ·
      refine ⟨39476921477045768964034715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105271790605455383904092573 39476921477045768964034715)
      ·
        refine ⟨59215382215568653446052073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39476921477045768964034715 59215382215568653446052073)
        ·
          refine ⟨44411536661676490084539055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59215382215568653446052073 44411536661676490084539055)
          ·
            refine ⟨66617304992514735126808583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44411536661676490084539055 66617304992514735126808583)
            ·
              refine ⟨99925957488772102690212875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66617304992514735126808583 99925957488772102690212875)
              ·
                refine ⟨149888936233158154035319313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99925957488772102690212875 149888936233158154035319313)
                ·
                  refine ⟨112416702174868615526489485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149888936233158154035319313 112416702174868615526489485)
                  ·
                    refine ⟨42156263315575730822433557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112416702174868615526489485 42156263315575730822433557)
                    ·
                      refine ⟨1976074842917612382301573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42156263315575730822433557 1976074842917612382301573)
                      ·
                        rfl

theorem cell23_3848392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_3848392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848392 prefixEnd_3848392 := by exact prefixLift 3848392
  have htrace : WordTrace (prefixWord ++ tailWord_3848392) baseStart_3848392 baseEnd_3848392 := by
    simpa [prefixWord, tailWord_3848392, baseEnd_3848392] using wordTrace_append hprefix tailTrace_3848392
  have hstable : (prefixWord ++ tailWord_3848392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848392).length < 2 ^ (prefixWord ++ tailWord_3848392).sum := by decide
  have hdescent : baseEnd_3848392 < baseStart_3848392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848406 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3848406 : Nat := 118140960795 + 3848406 * 2 ^ 59
def prefixEnd_3848406 : Nat := 4983230072969 + 3 ^ 40 * 3848406 * 2
def baseEnd_3848406 : Nat := 658694010548925109175503

theorem tailTrace_3848406 : CollatzResearch.WordTrace tailWord_3848406 prefixEnd_3848406 658694010548925109175503 := by
  unfold tailWord_3848406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772681130993112016445817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93575265397259861508755381 8772681130993112016445817)
  ·
    refine ⟨6579510848244834012334363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8772681130993112016445817 6579510848244834012334363)
    ·
      refine ⟨9869266272367251018501545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6579510848244834012334363 9869266272367251018501545)
      ·
        refine ⟨7401949704275438263876159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9869266272367251018501545 7401949704275438263876159)
        ·
          refine ⟨11102924556413157395814239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7401949704275438263876159 11102924556413157395814239)
          ·
            refine ⟨16654386834619736093721359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11102924556413157395814239 16654386834619736093721359)
            ·
              refine ⟨24981580251929604140582039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16654386834619736093721359 24981580251929604140582039)
              ·
                refine ⟨37472370377894406210873059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24981580251929604140582039 37472370377894406210873059)
                ·
                  refine ⟨56208555566841609316309589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37472370377894406210873059 56208555566841609316309589)
                  ·
                    refine ⟨658694010548925109175503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56208555566841609316309589 658694010548925109175503)
                    ·
                      rfl

theorem cell23_3848406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3848406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848406 prefixEnd_3848406 := by exact prefixLift 3848406
  have htrace : WordTrace (prefixWord ++ tailWord_3848406) baseStart_3848406 baseEnd_3848406 := by
    simpa [prefixWord, tailWord_3848406, baseEnd_3848406] using wordTrace_append hprefix tailTrace_3848406
  have hstable : (prefixWord ++ tailWord_3848406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848406).length < 2 ^ (prefixWord ++ tailWord_3848406).sum := by decide
  have hdescent : baseEnd_3848406 < baseStart_3848406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848413 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3848413 : Nat := 118140960795 + 3848413 * 2 ^ 59
def prefixEnd_3848413 : Nat := 4983230072969 + 3 ^ 40 * 3848413 * 2
def baseEnd_3848413 : Nat := 1976085626011356800138977

theorem tailTrace_3848413 : CollatzResearch.WordTrace tailWord_3848413 prefixEnd_3848413 1976085626011356800138977 := by
  unfold tailWord_3848413
  simp only [CollatzResearch.WordTrace]
  refine ⟨140363153406864432458637893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93575435604576288305758595 140363153406864432458637893)
  ·
    refine ⟨26318091263787081085994605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140363153406864432458637893 26318091263787081085994605)
    ·
      refine ⟨9869284223920155407247977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26318091263787081085994605 9869284223920155407247977)
      ·
        refine ⟨7401963167940116555435983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9869284223920155407247977 7401963167940116555435983)
        ·
          refine ⟨11102944751910174833153975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7401963167940116555435983 11102944751910174833153975)
          ·
            refine ⟨16654417127865262249730963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11102944751910174833153975 16654417127865262249730963)
            ·
              refine ⟨24981625691797893374596445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16654417127865262249730963 24981625691797893374596445)
              ·
                refine ⟨9368109634424210015473667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24981625691797893374596445 9368109634424210015473667)
                ·
                  refine ⟨14052164451636315023210501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9368109634424210015473667 14052164451636315023210501)
                  ·
                    refine ⟨2634780834681809066851969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14052164451636315023210501 2634780834681809066851969)
                    ·
                      refine ⟨1976085626011356800138977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634780834681809066851969 1976085626011356800138977)
                      ·
                        rfl

theorem cell23_3848413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3848413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848413 prefixEnd_3848413 := by exact prefixLift 3848413
  have htrace : WordTrace (prefixWord ++ tailWord_3848413) baseStart_3848413 baseEnd_3848413 := by
    simpa [prefixWord, tailWord_3848413, baseEnd_3848413] using wordTrace_append hprefix tailTrace_3848413
  have hstable : (prefixWord ++ tailWord_3848413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848413).length < 2 ^ (prefixWord ++ tailWord_3848413).sum := by decide
  have hdescent : baseEnd_3848413 < baseStart_3848413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848446 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3848446 : Nat := 118140960795 + 3848446 * 2 ^ 59
def prefixEnd_3848446 : Nat := 4983230072969 + 3 ^ 40 * 3848446 * 2
def baseEnd_3848446 : Nat := 1976102570872955171026325

theorem tailTrace_3848446 : CollatzResearch.WordTrace tailWord_3848446 prefixEnd_3848446 1976102570872955171026325 := by
  unfold tailWord_3848446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17545544626968109886823649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93576238010496586063059461 17545544626968109886823649)
  ·
    refine ⟨13159158470226082415117737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17545544626968109886823649 13159158470226082415117737)
    ·
      refine ⟨9869368852669561811338303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13159158470226082415117737 9869368852669561811338303)
      ·
        refine ⟨14804053279004342717007455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9869368852669561811338303 14804053279004342717007455)
        ·
          refine ⟨22206079918506514075511183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14804053279004342717007455 22206079918506514075511183)
          ·
            refine ⟨33309119877759771113266775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22206079918506514075511183 33309119877759771113266775)
            ·
              refine ⟨49963679816639656669900163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33309119877759771113266775 49963679816639656669900163)
              ·
                refine ⟨74945519724959485004850245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49963679816639656669900163 74945519724959485004850245)
                ·
                  refine ⟨14052284948429903438409421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74945519724959485004850245 14052284948429903438409421)
                  ·
                    refine ⟨5269606855661213789403533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14052284948429903438409421 5269606855661213789403533)
                    ·
                      refine ⟨1976102570872955171026325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5269606855661213789403533 1976102570872955171026325)
                      ·
                        rfl

theorem cell23_3848446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3848446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848446 prefixEnd_3848446 := by exact prefixLift 3848446
  have htrace : WordTrace (prefixWord ++ tailWord_3848446) baseStart_3848446 baseEnd_3848446 := by
    simpa [prefixWord, tailWord_3848446, baseEnd_3848446] using wordTrace_append hprefix tailTrace_3848446
  have hstable : (prefixWord ++ tailWord_3848446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848446).length < 2 ^ (prefixWord ++ tailWord_3848446).sum := by decide
  have hdescent : baseEnd_3848446 < baseStart_3848446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848449 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3848449 : Nat := 118140960795 + 3848449 * 2 ^ 59
def prefixEnd_3848449 : Nat := 4983230072969 + 3 ^ 40 * 3848449 * 2
def baseEnd_3848449 : Nat := 658701370438306219762937

theorem tailTrace_3848449 : CollatzResearch.WordTrace tailWord_3848449 prefixEnd_3848449 658701370438306219762937 := by
  unfold tailWord_3848449
  simp only [CollatzResearch.WordTrace]
  refine ⟨140364466434734010606948401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93576310956489340404632267 140364466434734010606948401)
  ·
    refine ⟨105273349826050507955211301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140364466434734010606948401 105273349826050507955211301)
    ·
      refine ⟨19738753092384470241602119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105273349826050507955211301 19738753092384470241602119)
      ·
        refine ⟨29608129638576705362403179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19738753092384470241602119 29608129638576705362403179)
        ·
          refine ⟨44412194457865058043604769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29608129638576705362403179 44412194457865058043604769)
          ·
            refine ⟨33309145843398793532703577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44412194457865058043604769 33309145843398793532703577)
            ·
              refine ⟨24981859382549095149527683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33309145843398793532703577 24981859382549095149527683)
              ·
                refine ⟨37472789073823642724291525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24981859382549095149527683 37472789073823642724291525)
                ·
                  refine ⟨7026147951341933010804661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37472789073823642724291525 7026147951341933010804661)
                  ·
                    refine ⟨658701370438306219762937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7026147951341933010804661 658701370438306219762937)
                    ·
                      rfl

theorem cell23_3848449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3848449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848449 prefixEnd_3848449 := by exact prefixLift 3848449
  have htrace : WordTrace (prefixWord ++ tailWord_3848449) baseStart_3848449 baseEnd_3848449 := by
    simpa [prefixWord, tailWord_3848449, baseEnd_3848449] using wordTrace_append hprefix tailTrace_3848449
  have hstable : (prefixWord ++ tailWord_3848449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848449).length < 2 ^ (prefixWord ++ tailWord_3848449).sum := by decide
  have hdescent : baseEnd_3848449 < baseStart_3848449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848469 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3848469 : Nat := 118140960795 + 3848469 * 2 ^ 59
def prefixEnd_3848469 : Nat := 4983230072969 + 3 ^ 40 * 3848469 * 2
def baseEnd_3848469 : Nat := 1976114380928008581038719

theorem tailTrace_3848469 : CollatzResearch.WordTrace tailWord_3848469 prefixEnd_3848469 1976114380928008581038719 := by
  unfold tailWord_3848469
  simp only [CollatzResearch.WordTrace]
  refine ⟨140365195894661554022676461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93576797263107702681784307 140365195894661554022676461)
  ·
    refine ⟨52636948460498082758503673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140365195894661554022676461 52636948460498082758503673)
    ·
      refine ⟨39477711345373562068877755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52636948460498082758503673 39477711345373562068877755)
      ·
        refine ⟨59216567018060343103316633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39477711345373562068877755 59216567018060343103316633)
        ·
          refine ⟨44412425263545257327487475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59216567018060343103316633 44412425263545257327487475)
          ·
            refine ⟨66618637895317885991231213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44412425263545257327487475 66618637895317885991231213)
            ·
              refine ⟨24981989210744207246711705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66618637895317885991231213 24981989210744207246711705)
              ·
                refine ⟨18736491908058155435033779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24981989210744207246711705 18736491908058155435033779)
                ·
                  refine ⟨28104737862087233152550669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18736491908058155435033779 28104737862087233152550669)
                  ·
                    refine ⟨10539276698282712432206501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28104737862087233152550669 10539276698282712432206501)
                    ·
                      refine ⟨1976114380928008581038719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10539276698282712432206501 1976114380928008581038719)
                      ·
                        rfl

theorem cell23_3848469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3848469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848469 prefixEnd_3848469 := by exact prefixLift 3848469
  have htrace : WordTrace (prefixWord ++ tailWord_3848469) baseStart_3848469 baseEnd_3848469 := by
    simpa [prefixWord, tailWord_3848469, baseEnd_3848469] using wordTrace_append hprefix tailTrace_3848469
  have hstable : (prefixWord ++ tailWord_3848469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848469).length < 2 ^ (prefixWord ++ tailWord_3848469).sum := by decide
  have hdescent : baseEnd_3848469 < baseStart_3848469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848506 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_3848506 : Nat := 118140960795 + 3848506 * 2 ^ 59
def prefixEnd_3848506 : Nat := 4983230072969 + 3 ^ 40 * 3848506 * 2
def baseEnd_3848506 : Nat := 1976133379712224936276049

theorem tailTrace_3848506 : CollatzResearch.WordTrace tailWord_3848506 prefixEnd_3848506 1976133379712224936276049 := by
  unfold tailWord_3848506
  simp only [CollatzResearch.WordTrace]
  refine ⟨35091636348881877335443343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93577696930351672894515581 35091636348881877335443343)
  ·
    refine ⟨52637454523322816003165015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35091636348881877335443343 52637454523322816003165015)
    ·
      refine ⟨78956181784984224004747523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52637454523322816003165015 78956181784984224004747523)
      ·
        refine ⟨118434272677476336007121285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78956181784984224004747523 118434272677476336007121285)
        ·
          refine ⟨22206426127026813001335241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118434272677476336007121285 22206426127026813001335241)
          ·
            refine ⟨16654819595270109751001431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22206426127026813001335241 16654819595270109751001431)
            ·
              refine ⟨24982229392905164626502147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16654819595270109751001431 24982229392905164626502147)
              ·
                refine ⟨37473344089357746939753221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24982229392905164626502147 37473344089357746939753221)
                ·
                  refine ⟨7026252016754577551203729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37473344089357746939753221 7026252016754577551203729)
                  ·
                    refine ⟨5269689012565933163402797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7026252016754577551203729 5269689012565933163402797)
                    ·
                      refine ⟨1976133379712224936276049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5269689012565933163402797 1976133379712224936276049)
                      ·
                        rfl

theorem cell23_3848506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_3848506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848506 prefixEnd_3848506 := by exact prefixLift 3848506
  have htrace : WordTrace (prefixWord ++ tailWord_3848506) baseStart_3848506 baseEnd_3848506 := by
    simpa [prefixWord, tailWord_3848506, baseEnd_3848506] using wordTrace_append hprefix tailTrace_3848506
  have hstable : (prefixWord ++ tailWord_3848506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848506).length < 2 ^ (prefixWord ++ tailWord_3848506).sum := by decide
  have hdescent : baseEnd_3848506 < baseStart_3848506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848569 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 5, 6]
def baseStart_3848569 : Nat := 118140960795 + 3848569 * 2 ^ 59
def prefixEnd_3848569 : Nat := 4983230072969 + 3 ^ 40 * 3848569 * 2
def baseEnd_3848569 : Nat := 658721909664486063262753

theorem tailTrace_3848569 : CollatzResearch.WordTrace tailWord_3848569 prefixEnd_3848569 658721909664486063262753 := by
  unfold tailWord_3848569
  simp only [CollatzResearch.WordTrace]
  refine ⟨140368843194299271101316761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93579228796199514067544507 140368843194299271101316761)
  ·
    refine ⟨105276632395724453325987571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140368843194299271101316761 105276632395724453325987571)
    ·
      refine ⟨157914948593586679988981357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105276632395724453325987571 157914948593586679988981357)
      ·
        refine ⟨59218105722595004995868009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157914948593586679988981357 59218105722595004995868009)
        ·
          refine ⟨44413579291946253746901007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59218105722595004995868009 44413579291946253746901007)
          ·
            refine ⟨66620368937919380620351511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44413579291946253746901007 66620368937919380620351511)
            ·
              refine ⟨99930553406879070930527267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66620368937919380620351511 99930553406879070930527267)
              ·
                refine ⟨149895830110318606395790901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99930553406879070930527267 149895830110318606395790901)
                ·
                  refine ⟨14052734072842369349605397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149895830110318606395790901 14052734072842369349605397)
                  ·
                    refine ⟨658721909664486063262753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14052734072842369349605397 658721909664486063262753)
                    ·
                      rfl

theorem cell23_3848569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_3848569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848569 prefixEnd_3848569 := by exact prefixLift 3848569
  have htrace : WordTrace (prefixWord ++ tailWord_3848569) baseStart_3848569 baseEnd_3848569 := by
    simpa [prefixWord, tailWord_3848569, baseEnd_3848569] using wordTrace_append hprefix tailTrace_3848569
  have hstable : (prefixWord ++ tailWord_3848569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848569).length < 2 ^ (prefixWord ++ tailWord_3848569).sum := by decide
  have hdescent : baseEnd_3848569 < baseStart_3848569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848576 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 4, 6, 2]
def baseStart_3848576 : Nat := 118140960795 + 3848576 * 2 ^ 59
def prefixEnd_3848576 : Nat := 4983230072969 + 3 ^ 40 * 3848576 * 2
def baseEnd_3848576 : Nat := 1976169323358039662400727

theorem tailTrace_3848576 : CollatzResearch.WordTrace tailWord_3848576 prefixEnd_3848576 1976169323358039662400727 := by
  unfold tailWord_3848576
  simp only [CollatzResearch.WordTrace]
  refine ⟨70184549252636955648410791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93579399003515940864547721 70184549252636955648410791)
  ·
    refine ⟨105276823878955433472616187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70184549252636955648410791 105276823878955433472616187)
    ·
      refine ⟨157915235818433150208924281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105276823878955433472616187 157915235818433150208924281)
      ·
        refine ⟨118436426863824862656693211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157915235818433150208924281 118436426863824862656693211)
        ·
          refine ⟨177654640295737293985039817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118436426863824862656693211 177654640295737293985039817)
          ·
            refine ⟨133240980221802970488779863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177654640295737293985039817 133240980221802970488779863)
            ·
              refine ⟨199861470332704455733169795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133240980221802970488779863 199861470332704455733169795)
              ·
                refine ⟨299792205499056683599754693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199861470332704455733169795 299792205499056683599754693)
                ·
                  refine ⟨56211038531073128174954005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299792205499056683599754693 56211038531073128174954005)
                  ·
                    refine ⟨2634892431144052883200969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56211038531073128174954005 2634892431144052883200969)
                    ·
                      refine ⟨1976169323358039662400727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634892431144052883200969 1976169323358039662400727)
                      ·
                        rfl

theorem cell23_3848576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_3848576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848576 prefixEnd_3848576 := by exact prefixLift 3848576
  have htrace : WordTrace (prefixWord ++ tailWord_3848576) baseStart_3848576 baseEnd_3848576 := by
    simpa [prefixWord, tailWord_3848576, baseEnd_3848576] using wordTrace_append hprefix tailTrace_3848576
  have hstable : (prefixWord ++ tailWord_3848576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848576).length < 2 ^ (prefixWord ++ tailWord_3848576).sum := by decide
  have hdescent : baseEnd_3848576 < baseStart_3848576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848599 : List Nat := [1, 1, 3, 3, 1, 1, 2, 11]
def baseStart_3848599 : Nat := 118140960795 + 3848599 * 2 ^ 59
def prefixEnd_3848599 : Nat := 4983230072969 + 3 ^ 40 * 3848599 * 2
def baseEnd_3848599 : Nat := 73191893830114558237523

theorem tailTrace_3848599 : CollatzResearch.WordTrace tailWord_3848599 prefixEnd_3848599 73191893830114558237523 := by
  unfold tailWord_3848599
  simp only [CollatzResearch.WordTrace]
  refine ⟨140369937384190586224908851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93579958256127057483272567 140369937384190586224908851)
  ·
    refine ⟨210554906076285879337363277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140369937384190586224908851 210554906076285879337363277)
    ·
      refine ⟨78958089778607204751511229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210554906076285879337363277 78958089778607204751511229)
      ·
        refine ⟨29609283666977701781816711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78958089778607204751511229 29609283666977701781816711)
        ·
          refine ⟨44413925500466552672725067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29609283666977701781816711 44413925500466552672725067)
          ·
            refine ⟨66620888250699829009087601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44413925500466552672725067 66620888250699829009087601)
            ·
              refine ⟨49965666188024871756815701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66620888250699829009087601 49965666188024871756815701)
              ·
                refine ⟨73191893830114558237523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 49965666188024871756815701 73191893830114558237523)
                ·
                  rfl

theorem cell23_3848599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 11].length) (baseStart_3848599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848599 prefixEnd_3848599 := by exact prefixLift 3848599
  have htrace : WordTrace (prefixWord ++ tailWord_3848599) baseStart_3848599 baseEnd_3848599 := by
    simpa [prefixWord, tailWord_3848599, baseEnd_3848599] using wordTrace_append hprefix tailTrace_3848599
  have hstable : (prefixWord ++ tailWord_3848599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848599).length < 2 ^ (prefixWord ++ tailWord_3848599).sum := by decide
  have hdescent : baseEnd_3848599 < baseStart_3848599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848610 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_3848610 : Nat := 118140960795 + 3848610 * 2 ^ 59
def prefixEnd_3848610 : Nat := 4983230072969 + 3 ^ 40 * 3848610 * 2
def baseEnd_3848610 : Nat := 1976186781700292529375571

theorem tailTrace_3848610 : CollatzResearch.WordTrace tailWord_3848610 prefixEnd_3848610 1976186781700292529375571 := by
  unfold tailWord_3848610
  simp only [CollatzResearch.WordTrace]
  refine ⟨35092584646787683775889821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93580225724767156735706189 35092584646787683775889821)
  ·
    refine ⟨13159719242545381415958683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35092584646787683775889821 13159719242545381415958683)
    ·
      refine ⟨19739578863818072123938025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13159719242545381415958683 19739578863818072123938025)
      ·
        refine ⟨14804684147863554092953519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19739578863818072123938025 14804684147863554092953519)
        ·
          refine ⟨22207026221795331139430279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14804684147863554092953519 22207026221795331139430279)
          ·
            refine ⟨33310539332692996709145419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22207026221795331139430279 33310539332692996709145419)
            ·
              refine ⟨49965808999039495063718129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33310539332692996709145419 49965808999039495063718129)
              ·
                refine ⟨37474356749279621297788597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49965808999039495063718129 37474356749279621297788597)
                ·
                  refine ⟨3513220945244964496667681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37474356749279621297788597 3513220945244964496667681)
                  ·
                    refine ⟨2634915708933723372500761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3513220945244964496667681 2634915708933723372500761)
                    ·
                      refine ⟨1976186781700292529375571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2634915708933723372500761 1976186781700292529375571)
                      ·
                        rfl

theorem cell23_3848610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_3848610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848610 prefixEnd_3848610 := by exact prefixLift 3848610
  have htrace : WordTrace (prefixWord ++ tailWord_3848610) baseStart_3848610 baseEnd_3848610 := by
    simpa [prefixWord, tailWord_3848610, baseEnd_3848610] using wordTrace_append hprefix tailTrace_3848610
  have hstable : (prefixWord ++ tailWord_3848610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848610).length < 2 ^ (prefixWord ++ tailWord_3848610).sum := by decide
  have hdescent : baseEnd_3848610 < baseStart_3848610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848613 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 3]
def baseStart_3848613 : Nat := 118140960795 + 3848613 * 2 ^ 59
def prefixEnd_3848613 : Nat := 4983230072969 + 3 ^ 40 * 3848613 * 2
def baseEnd_3848613 : Nat := 1976188322142256017638057

theorem tailTrace_3848613 : CollatzResearch.WordTrace tailWord_3848613 prefixEnd_3848613 1976188322142256017638057 := by
  unfold tailWord_3848613
  simp only [CollatzResearch.WordTrace]
  refine ⟨140370448006139866615918493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93580298670759911077278995 140370448006139866615918493)
  ·
    refine ⟨52638918002302449980969435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140370448006139866615918493 52638918002302449980969435)
    ·
      refine ⟨78958377003453674971454153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52638918002302449980969435 78958377003453674971454153)
      ·
        refine ⟨59218782752590256228590615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78958377003453674971454153 59218782752590256228590615)
        ·
          refine ⟨88828174128885384342885923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59218782752590256228590615 88828174128885384342885923)
          ·
            refine ⟨133242261193328076514328885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88828174128885384342885923 133242261193328076514328885)
            ·
              refine ⟨12491461986874507173218333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133242261193328076514328885 12491461986874507173218333)
              ·
                refine ⟨4684298245077940189956875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12491461986874507173218333 4684298245077940189956875)
                ·
                  refine ⟨7026447367616910284935313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684298245077940189956875 7026447367616910284935313)
                  ·
                    refine ⟨5269835525712682713701485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7026447367616910284935313 5269835525712682713701485)
                    ·
                      refine ⟨1976188322142256017638057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5269835525712682713701485 1976188322142256017638057)
                      ·
                        rfl

theorem cell23_3848613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_3848613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848613 prefixEnd_3848613 := by exact prefixLift 3848613
  have htrace : WordTrace (prefixWord ++ tailWord_3848613) baseStart_3848613 baseEnd_3848613 := by
    simpa [prefixWord, tailWord_3848613, baseEnd_3848613] using wordTrace_append hprefix tailTrace_3848613
  have hstable : (prefixWord ++ tailWord_3848613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848613).length < 2 ^ (prefixWord ++ tailWord_3848613).sum := by decide
  have hdescent : baseEnd_3848613 < baseStart_3848613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848660 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3848660 : Nat := 118140960795 + 3848660 * 2 ^ 59
def prefixEnd_3848660 : Nat := 4983230072969 + 3 ^ 40 * 3848660 * 2
def baseEnd_3848660 : Nat := 1976212455733017333750341

theorem tailTrace_3848660 : CollatzResearch.WordTrace tailWord_3848660 prefixEnd_3848660 1976212455733017333750341 := by
  unfold tailWord_3848660
  simp only [CollatzResearch.WordTrace]
  refine ⟨70186081118484796821439717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93581441491313062428586289 70186081118484796821439717)
  ·
    refine ⟨13159890209715899404019947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70186081118484796821439717 13159890209715899404019947)
    ·
      refine ⟨19739835314573849106029921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13159890209715899404019947 19739835314573849106029921)
      ·
        refine ⟨14804876485930386829522441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19739835314573849106029921 14804876485930386829522441)
        ·
          refine ⟨11103657364447790122141831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14804876485930386829522441 11103657364447790122141831)
          ·
            refine ⟨16655486046671685183212747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11103657364447790122141831 16655486046671685183212747)
            ·
              refine ⟨24983229070007527774819121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16655486046671685183212747 24983229070007527774819121)
              ·
                refine ⟨18737421802505645831114341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24983229070007527774819121 18737421802505645831114341)
                ·
                  refine ⟨3513266587969808593333939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18737421802505645831114341 3513266587969808593333939)
                  ·
                    refine ⟨5269899881954712890000909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3513266587969808593333939 5269899881954712890000909)
                    ·
                      refine ⟨1976212455733017333750341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5269899881954712890000909 1976212455733017333750341)
                      ·
                        rfl

theorem cell23_3848660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3848660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848660 prefixEnd_3848660 := by exact prefixLift 3848660
  have htrace : WordTrace (prefixWord ++ tailWord_3848660) baseStart_3848660 baseEnd_3848660 := by
    simpa [prefixWord, tailWord_3848660, baseEnd_3848660] using wordTrace_append hprefix tailTrace_3848660
  have hstable : (prefixWord ++ tailWord_3848660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848660).length < 2 ^ (prefixWord ++ tailWord_3848660).sum := by decide
  have hdescent : baseEnd_3848660 < baseStart_3848660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848696 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_3848696 : Nat := 118140960795 + 3848696 * 2 ^ 59
def prefixEnd_3848696 : Nat := 4983230072969 + 3 ^ 40 * 3848696 * 2
def baseEnd_3848696 : Nat := 1976230941036579192900175

theorem tailTrace_3848696 : CollatzResearch.WordTrace tailWord_3848696 prefixEnd_3848696 1976230941036579192900175 := by
  unfold tailWord_3848696
  simp only [CollatzResearch.WordTrace]
  refine ⟨70186737632419585895594971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93582316843226114527459961 70186737632419585895594971)
  ·
    refine ⟨105280106448629378843392457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70186737632419585895594971 105280106448629378843392457)
    ·
      refine ⟨78960079836472034132544343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105280106448629378843392457 78960079836472034132544343)
      ·
        refine ⟨118440119754708051198816515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78960079836472034132544343 118440119754708051198816515)
        ·
          refine ⟨177660179632062076798224773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118440119754708051198816515 177660179632062076798224773)
          ·
            refine ⟨33311283681011639399667145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177660179632062076798224773 33311283681011639399667145)
            ·
              refine ⟨24983462760758729549750359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33311283681011639399667145 24983462760758729549750359)
              ·
                refine ⟨37475194141138094324625539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24983462760758729549750359 37475194141138094324625539)
                ·
                  refine ⟨56212791211707141486938309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37475194141138094324625539 56212791211707141486938309)
                  ·
                    refine ⟨10539898352195089028800933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56212791211707141486938309 10539898352195089028800933)
                    ·
                      refine ⟨1976230941036579192900175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10539898352195089028800933 1976230941036579192900175)
                      ·
                        rfl

theorem cell23_3848696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_3848696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848696 prefixEnd_3848696 := by exact prefixLift 3848696
  have htrace : WordTrace (prefixWord ++ tailWord_3848696) baseStart_3848696 baseEnd_3848696 := by
    simpa [prefixWord, tailWord_3848696, baseEnd_3848696] using wordTrace_append hprefix tailTrace_3848696
  have hstable : (prefixWord ++ tailWord_3848696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848696).length < 2 ^ (prefixWord ++ tailWord_3848696).sum := by decide
  have hdescent : baseEnd_3848696 < baseStart_3848696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848723 : List Nat := [1, 1, 1, 2, 1, 5, 2, 5, 5]
def baseStart_3848723 : Nat := 118140960795 + 3848723 * 2 ^ 59
def prefixEnd_3848723 : Nat := 4983230072969 + 3 ^ 40 * 3848723 * 2
def baseEnd_3848723 : Nat := 219582756112694509695839

theorem tailTrace_3848723 : CollatzResearch.WordTrace tailWord_3848723 prefixEnd_3848723 219582756112694509695839 := by
  unfold tailWord_3848723
  simp only [CollatzResearch.WordTrace]
  refine ⟨140374460035741355402422823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93582973357160903601615215 140374460035741355402422823)
  ·
    refine ⟨210561690053612033103634235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140374460035741355402422823 210561690053612033103634235)
    ·
      refine ⟨315842535080418049655451353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210561690053612033103634235 315842535080418049655451353)
      ·
        refine ⟨236881901310313537241588515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315842535080418049655451353 236881901310313537241588515)
        ·
          refine ⟨355322851965470305862382773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236881901310313537241588515 355322851965470305862382773)
          ·
            refine ⟨33311517371762841174598385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355322851965470305862382773 33311517371762841174598385)
            ·
              refine ⟨24983638028822130880948789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33311517371762841174598385 24983638028822130880948789)
              ·
                refine ⟨2342216065202074770088949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24983638028822130880948789 2342216065202074770088949)
                ·
                  refine ⟨219582756112694509695839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342216065202074770088949 219582756112694509695839)
                  ·
                    rfl

theorem cell23_3848723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 5].length) (baseStart_3848723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848723 prefixEnd_3848723 := by exact prefixLift 3848723
  have htrace : WordTrace (prefixWord ++ tailWord_3848723) baseStart_3848723 baseEnd_3848723 := by
    simpa [prefixWord, tailWord_3848723, baseEnd_3848723] using wordTrace_append hprefix tailTrace_3848723
  have hstable : (prefixWord ++ tailWord_3848723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848723).length < 2 ^ (prefixWord ++ tailWord_3848723).sum := by decide
  have hdescent : baseEnd_3848723 < baseStart_3848723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848773 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_3848773 : Nat := 118140960795 + 3848773 * 2 ^ 59
def prefixEnd_3848773 : Nat := 4983230072969 + 3 ^ 40 * 3848773 * 2
def baseEnd_3848773 : Nat := 1976270479046975391637321

theorem tailTrace_3848773 : CollatzResearch.WordTrace tailWord_3848773 prefixEnd_3848773 1976270479046975391637321 := by
  unfold tailWord_3848773
  simp only [CollatzResearch.WordTrace]
  refine ⟨140376283685560213941742973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93584189123706809294495315 140376283685560213941742973)
  ·
    refine ⟨52641106382085080228153615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140376283685560213941742973 52641106382085080228153615)
    ·
      refine ⟨78961659573127620342230423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52641106382085080228153615 78961659573127620342230423)
      ·
        refine ⟨118442489359691430513345635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78961659573127620342230423 118442489359691430513345635)
        ·
          refine ⟨177663734039537145770018453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118442489359691430513345635 177663734039537145770018453)
          ·
            refine ⟨8327987533103303707969615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177663734039537145770018453 8327987533103303707969615)
            ·
              refine ⟨12491981299654955561954423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8327987533103303707969615 12491981299654955561954423)
              ·
                refine ⟨18737971949482433342931635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12491981299654955561954423 18737971949482433342931635)
                ·
                  refine ⟨28106957924223650014397453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18737971949482433342931635 28106957924223650014397453)
                  ·
                    refine ⟨10540109221583868755399045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28106957924223650014397453 10540109221583868755399045)
                    ·
                      refine ⟨1976270479046975391637321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10540109221583868755399045 1976270479046975391637321)
                      ·
                        rfl

theorem cell23_3848773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_3848773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848773 prefixEnd_3848773 := by exact prefixLift 3848773
  have htrace : WordTrace (prefixWord ++ tailWord_3848773) baseStart_3848773 baseEnd_3848773 := by
    simpa [prefixWord, tailWord_3848773, baseEnd_3848773] using wordTrace_append hprefix tailTrace_3848773
  have hstable : (prefixWord ++ tailWord_3848773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848773).length < 2 ^ (prefixWord ++ tailWord_3848773).sum := by decide
  have hdescent : baseEnd_3848773 < baseStart_3848773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848774 : List Nat := [6, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3848774 : Nat := 118140960795 + 3848774 * 2 ^ 59
def prefixEnd_3848774 : Nat := 4983230072969 + 3 ^ 40 * 3848774 * 2
def baseEnd_3848774 : Nat := 219585665836403320858313

theorem tailTrace_3848774 : CollatzResearch.WordTrace tailWord_3848774 prefixEnd_3848774 219585665836403320858313 := by
  unfold tailWord_3848774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386760004954893472266543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93584213439037727408352917 4386760004954893472266543)
  ·
    refine ⟨6580140007432340208399815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4386760004954893472266543 6580140007432340208399815)
    ·
      refine ⟨9870210011148510312599723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6580140007432340208399815 9870210011148510312599723)
      ·
        refine ⟨14805315016722765468899585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9870210011148510312599723 14805315016722765468899585)
        ·
          refine ⟨11103986262542074101674689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14805315016722765468899585 11103986262542074101674689)
          ·
            refine ⟨8327989696906555576256017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11103986262542074101674689 8327989696906555576256017)
            ·
              refine ⟨6245992272679916682192013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8327989696906555576256017 6245992272679916682192013)
              ·
                refine ⟨2342247102254968755822005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6245992272679916682192013 2342247102254968755822005)
                ·
                  refine ⟨219585665836403320858313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342247102254968755822005 219585665836403320858313)
                  ·
                    rfl

theorem cell23_3848774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3848774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848774 prefixEnd_3848774 := by exact prefixLift 3848774
  have htrace : WordTrace (prefixWord ++ tailWord_3848774) baseStart_3848774 baseEnd_3848774 := by
    simpa [prefixWord, tailWord_3848774, baseEnd_3848774] using wordTrace_append hprefix tailTrace_3848774
  have hstable : (prefixWord ++ tailWord_3848774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848774).length < 2 ^ (prefixWord ++ tailWord_3848774).sum := by decide
  have hdescent : baseEnd_3848774 < baseStart_3848774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848864 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 6]
def baseStart_3848864 : Nat := 118140960795 + 3848864 * 2 ^ 59
def prefixEnd_3848864 : Nat := 4983230072969 + 3 ^ 40 * 3848864 * 2
def baseEnd_3848864 : Nat := 219590800642948281733267

theorem tailTrace_3848864 : CollatzResearch.WordTrace tailWord_3848864 prefixEnd_3848864 219590800642948281733267 := by
  unfold tailWord_3848864
  simp only [CollatzResearch.WordTrace]
  refine ⟨70189801364115268241652823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93586401818820357655537097 70189801364115268241652823)
  ·
    refine ⟨105284702046172902362479235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70189801364115268241652823 105284702046172902362479235)
    ·
      refine ⟨157927053069259353543718853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105284702046172902362479235 157927053069259353543718853)
      ·
        refine ⟨29611322450486128789447285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157927053069259353543718853 29611322450486128789447285)
        ·
          refine ⟨2776061479733074574010683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29611322450486128789447285 2776061479733074574010683)
          ·
            refine ⟨4164092219599611861016025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776061479733074574010683 4164092219599611861016025)
            ·
              refine ⟨3123069164699708895762019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164092219599611861016025 3123069164699708895762019)
              ·
                refine ⟨4684603747049563343643029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123069164699708895762019 4684603747049563343643029)
                ·
                  refine ⟨219590800642948281733267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4684603747049563343643029 219590800642948281733267)
                  ·
                    rfl

theorem cell23_3848864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 6].length) (baseStart_3848864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848864 prefixEnd_3848864 := by exact prefixLift 3848864
  have htrace : WordTrace (prefixWord ++ tailWord_3848864) baseStart_3848864 baseEnd_3848864 := by
    simpa [prefixWord, tailWord_3848864, baseEnd_3848864] using wordTrace_append hprefix tailTrace_3848864
  have hstable : (prefixWord ++ tailWord_3848864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848864).length < 2 ^ (prefixWord ++ tailWord_3848864).sum := by decide
  have hdescent : baseEnd_3848864 < baseStart_3848864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848877 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_3848877 : Nat := 118140960795 + 3848877 * 2 ^ 59
def prefixEnd_3848877 : Nat := 4983230072969 + 3 ^ 40 * 3848877 * 2
def baseEnd_3848877 : Nat := 658774627011680994912281

theorem tailTrace_3848877 : CollatzResearch.WordTrace tailWord_3848877 prefixEnd_3848877 658774627011680994912281 := by
  unfold tailWord_3848877
  simp only [CollatzResearch.WordTrace]
  refine ⟨140380076877183439703528885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93586717918122293135685923 140380076877183439703528885)
  ·
    refine ⟨13160632207235947472205833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140380076877183439703528885 13160632207235947472205833)
    ·
      refine ⟨9870474155426960604154375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13160632207235947472205833 9870474155426960604154375)
      ·
        refine ⟨14805711233140440906231563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9870474155426960604154375 14805711233140440906231563)
        ·
          refine ⟨22208566849710661359347345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14805711233140440906231563 22208566849710661359347345)
          ·
            refine ⟨16656425137282996019510509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22208566849710661359347345 16656425137282996019510509)
            ·
              refine ⟨6246159426481123507316441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16656425137282996019510509 6246159426481123507316441)
              ·
                refine ⟨4684619569860842630487331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6246159426481123507316441 4684619569860842630487331)
                ·
                  refine ⟨7026929354791263945730997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684619569860842630487331 7026929354791263945730997)
                  ·
                    refine ⟨658774627011680994912281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7026929354791263945730997 658774627011680994912281)
                    ·
                      rfl

theorem cell23_3848877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_3848877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848877 prefixEnd_3848877 := by exact prefixLift 3848877
  have htrace : WordTrace (prefixWord ++ tailWord_3848877) baseStart_3848877 baseEnd_3848877 := by
    simpa [prefixWord, tailWord_3848877, baseEnd_3848877] using wordTrace_append hprefix tailTrace_3848877
  have hstable : (prefixWord ++ tailWord_3848877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848877).length < 2 ^ (prefixWord ++ tailWord_3848877).sum := by decide
  have hdescent : baseEnd_3848877 < baseStart_3848877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848902 : List Nat := [6, 1, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3848902 : Nat := 118140960795 + 3848902 * 2 ^ 59
def prefixEnd_3848902 : Nat := 4983230072969 + 3 ^ 40 * 3848902 * 2
def baseEnd_3848902 : Nat := 658778906017135128974743

theorem tailTrace_3848902 : CollatzResearch.WordTrace tailWord_3848902 prefixEnd_3848902 658778906017135128974743 := by
  unfold tailWord_3848902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386905896940402155412155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93587325801395245982125973 4386905896940402155412155)
  ·
    refine ⟨6580358845410603233118233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4386905896940402155412155 6580358845410603233118233)
    ·
      refine ⟨4935269134057952424838675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6580358845410603233118233 4935269134057952424838675)
      ·
        refine ⟨7402903701086928637258013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4935269134057952424838675 7402903701086928637258013)
        ·
          refine ⟨2776088887907598238971755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7402903701086928637258013 2776088887907598238971755)
          ·
            refine ⟨4164133331861397358457633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776088887907598238971755 4164133331861397358457633)
            ·
              refine ⟨3123099998896048018843225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164133331861397358457633 3123099998896048018843225)
              ·
                refine ⟨2342324999172036014132419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123099998896048018843225 2342324999172036014132419)
                ·
                  refine ⟨3513487498758054021198629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342324999172036014132419 3513487498758054021198629)
                  ·
                    refine ⟨658778906017135128974743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3513487498758054021198629 658778906017135128974743)
                    ·
                      rfl

theorem cell23_3848902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3848902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848902 prefixEnd_3848902 := by exact prefixLift 3848902
  have htrace : WordTrace (prefixWord ++ tailWord_3848902) baseStart_3848902 baseEnd_3848902 := by
    simpa [prefixWord, tailWord_3848902, baseEnd_3848902] using wordTrace_append hprefix tailTrace_3848902
  have hstable : (prefixWord ++ tailWord_3848902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848902).length < 2 ^ (prefixWord ++ tailWord_3848902).sum := by decide
  have hdescent : baseEnd_3848902 < baseStart_3848902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848908 : List Nat := [2, 2, 1, 5, 1, 3, 2, 2, 1, 1, 3]
def baseStart_3848908 : Nat := 118140960795 + 3848908 * 2 ^ 59
def prefixEnd_3848908 : Nat := 4983230072969 + 3 ^ 40 * 3848908 * 2
def baseEnd_3848908 : Nat := 1976339798935332363449201

theorem tailTrace_3848908 : CollatzResearch.WordTrace tailWord_3848908 prefixEnd_3848908 1976339798935332363449201 := by
  unfold tailWord_3848908
  simp only [CollatzResearch.WordTrace]
  refine ⟨70190603770035565998953689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93587471693380754665271585 70190603770035565998953689)
  ·
    refine ⟨52642952827526674499215267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70190603770035565998953689 52642952827526674499215267)
    ·
      refine ⟨78964429241290011748822901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52642952827526674499215267 78964429241290011748822901)
      ·
        refine ⟨7402915241370938601452147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78964429241290011748822901 7402915241370938601452147)
        ·
          refine ⟨11104372862056407902178221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402915241370938601452147 11104372862056407902178221)
          ·
            refine ⟨4164139823271152963316833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11104372862056407902178221 4164139823271152963316833)
            ·
              refine ⟨3123104867453364722487625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164139823271152963316833 3123104867453364722487625)
              ·
                refine ⟨2342328650590023541865719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123104867453364722487625 2342328650590023541865719)
                ·
                  refine ⟨3513492975885035312798579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342328650590023541865719 3513492975885035312798579)
                  ·
                    refine ⟨5270239463827552969197869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3513492975885035312798579 5270239463827552969197869)
                    ·
                      refine ⟨1976339798935332363449201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5270239463827552969197869 1976339798935332363449201)
                      ·
                        rfl

theorem cell23_3848908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_3848908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848908 prefixEnd_3848908 := by exact prefixLift 3848908
  have htrace : WordTrace (prefixWord ++ tailWord_3848908) baseStart_3848908 baseEnd_3848908 := by
    simpa [prefixWord, tailWord_3848908, baseEnd_3848908] using wordTrace_append hprefix tailTrace_3848908
  have hstable : (prefixWord ++ tailWord_3848908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848908).length < 2 ^ (prefixWord ++ tailWord_3848908).sum := by decide
  have hdescent : baseEnd_3848908 < baseStart_3848908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848920 : List Nat := [2, 1, 2, 2, 3, 4, 1, 8]
def baseStart_3848920 : Nat := 118140960795 + 3848920 * 2 ^ 59
def prefixEnd_3848920 : Nat := 4983230072969 + 3 ^ 40 * 3848920 * 2
def baseEnd_3848920 : Nat := 73197998544562456166635

theorem tailTrace_3848920 : CollatzResearch.WordTrace tailWord_3848920 prefixEnd_3848920 73197998544562456166635 := by
  unfold tailWord_3848920
  simp only [CollatzResearch.WordTrace]
  refine ⟨70190822608013829023672107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93587763477351772031562809 70190822608013829023672107)
  ·
    refine ⟨105286233912020743535508161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70190822608013829023672107 105286233912020743535508161)
    ·
      refine ⟨78964675434015557651631121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105286233912020743535508161 78964675434015557651631121)
      ·
        refine ⟨59223506575511668238723341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78964675434015557651631121 59223506575511668238723341)
        ·
          refine ⟨22208814965816875589521253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59223506575511668238723341 22208814965816875589521253)
          ·
            refine ⟨4164152806090664173035235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22208814965816875589521253 4164152806090664173035235)
            ·
              refine ⟨6246229209135996259552853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164152806090664173035235 6246229209135996259552853)
              ·
                refine ⟨73197998544562456166635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6246229209135996259552853 73197998544562456166635)
                ·
                  rfl

theorem cell23_3848920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 8].length) (baseStart_3848920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848920 prefixEnd_3848920 := by exact prefixLift 3848920
  have htrace : WordTrace (prefixWord ++ tailWord_3848920) baseStart_3848920 baseEnd_3848920 := by
    simpa [prefixWord, tailWord_3848920, baseEnd_3848920] using wordTrace_append hprefix tailTrace_3848920
  have hstable : (prefixWord ++ tailWord_3848920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848920).length < 2 ^ (prefixWord ++ tailWord_3848920).sum := by decide
  have hdescent : baseEnd_3848920 < baseStart_3848920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848924 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3848924 : Nat := 118140960795 + 3848924 * 2 ^ 59
def prefixEnd_3848924 : Nat := 4983230072969 + 3 ^ 40 * 3848924 * 2
def baseEnd_3848924 : Nat := 658782671541934766949709

theorem tailTrace_3848924 : CollatzResearch.WordTrace tailWord_3848924 prefixEnd_3848924 658782671541934766949709 := by
  unfold tailWord_3848924
  simp only [CollatzResearch.WordTrace]
  refine ⟨70190895554006583365244913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93587860738675444486993217 70190895554006583365244913)
  ·
    refine ⟨52643171665504937523933685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70190895554006583365244913 52643171665504937523933685)
    ·
      refine ⟨4935297343641087892868783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52643171665504937523933685 4935297343641087892868783)
      ·
        refine ⟨7402946015461631839303175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4935297343641087892868783 7402946015461631839303175)
        ·
          refine ⟨11104419023192447758954763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402946015461631839303175 11104419023192447758954763)
          ·
            refine ⟨16656628534788671638432145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11104419023192447758954763 16656628534788671638432145)
            ·
              refine ⟨12492471401091503728824109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16656628534788671638432145 12492471401091503728824109)
              ·
                refine ⟨4684676775409313898309041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12492471401091503728824109 4684676775409313898309041)
                ·
                  refine ⟨3513507581556985423731781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4684676775409313898309041 3513507581556985423731781)
                  ·
                    refine ⟨658782671541934766949709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3513507581556985423731781 658782671541934766949709)
                    ·
                      rfl

theorem cell23_3848924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3848924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848924 prefixEnd_3848924 := by exact prefixLift 3848924
  have htrace : WordTrace (prefixWord ++ tailWord_3848924) baseStart_3848924 baseEnd_3848924 := by
    simpa [prefixWord, tailWord_3848924, baseEnd_3848924] using wordTrace_append hprefix tailTrace_3848924
  have hstable : (prefixWord ++ tailWord_3848924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848924).length < 2 ^ (prefixWord ++ tailWord_3848924).sum := by decide
  have hdescent : baseEnd_3848924 < baseStart_3848924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3848987 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 8, 2, 2]
def baseStart_3848987 : Nat := 118140960795 + 3848987 * 2 ^ 59
def prefixEnd_3848987 : Nat := 4983230072969 + 3 ^ 40 * 3848987 * 2
def baseEnd_3848987 : Nat := 1976380363907037554361337

theorem tailTrace_3848987 : CollatzResearch.WordTrace tailWord_3848987 prefixEnd_3848987 1976380363907037554361337 := by
  unfold tailWord_3848987
  simp only [CollatzResearch.WordTrace]
  refine ⟨140384088906784928490033215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93589392604523285660022143 140384088906784928490033215)
  ·
    refine ⟨210576133360177392735049823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140384088906784928490033215 210576133360177392735049823)
    ·
      refine ⟨315864200040266089102574735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210576133360177392735049823 315864200040266089102574735)
      ·
        refine ⟨473796300060399133653862103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315864200040266089102574735 473796300060399133653862103)
        ·
          refine ⟨710694450090598700480793155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473796300060399133653862103 710694450090598700480793155)
          ·
            refine ⟨1066041675135898050721189733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710694450090598700480793155 1066041675135898050721189733)
            ·
              refine ⟨199882814087980884510223075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1066041675135898050721189733 199882814087980884510223075)
              ·
                refine ⟨299824221131971326765334613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199882814087980884510223075 299824221131971326765334613)
                ·
                  refine ⟨3513565091390288985531265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 299824221131971326765334613 3513565091390288985531265)
                  ·
                    refine ⟨2635173818542716739148449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3513565091390288985531265 2635173818542716739148449)
                    ·
                      refine ⟨1976380363907037554361337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2635173818542716739148449 1976380363907037554361337)
                      ·
                        rfl

theorem cell23_3848987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 2, 2].length) (baseStart_3848987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3848987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3848987 prefixEnd_3848987 := by exact prefixLift 3848987
  have htrace : WordTrace (prefixWord ++ tailWord_3848987) baseStart_3848987 baseEnd_3848987 := by
    simpa [prefixWord, tailWord_3848987, baseEnd_3848987] using wordTrace_append hprefix tailTrace_3848987
  have hstable : (prefixWord ++ tailWord_3848987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3848987).length < 2 ^ (prefixWord ++ tailWord_3848987).sum := by decide
  have hdescent : baseEnd_3848987 < baseStart_3848987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3848987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849003 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 7]
def baseStart_3849003 : Nat := 118140960795 + 3849003 * 2 ^ 59
def prefixEnd_3849003 : Nat := 4983230072969 + 3 ^ 40 * 3849003 * 2
def baseEnd_3849003 : Nat := 1976388579597509491761263

theorem tailTrace_3849003 : CollatzResearch.WordTrace tailWord_3849003 prefixEnd_3849003 1976388579597509491761263 := by
  unfold tailWord_3849003
  simp only [CollatzResearch.WordTrace]
  refine ⟨140384672474726963222615663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93589781649817975481743775 140384672474726963222615663)
  ·
    refine ⟨210577008712090444833923495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140384672474726963222615663 210577008712090444833923495)
    ·
      refine ⟨315865513068135667250885243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210577008712090444833923495 315865513068135667250885243)
      ·
        refine ⟨473798269602203500876327865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315865513068135667250885243 473798269602203500876327865)
        ·
          refine ⟨355348702201652625657245899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473798269602203500876327865 355348702201652625657245899)
          ·
            refine ⟨533023053302478938485868849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355348702201652625657245899 533023053302478938485868849)
            ·
              refine ⟨399767289976859203864401637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533023053302478938485868849 399767289976859203864401637)
              ·
                refine ⟨74956366870661100724575307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399767289976859203864401637 74956366870661100724575307)
                ·
                  refine ⟨112434550305991651086862961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74956366870661100724575307 112434550305991651086862961)
                  ·
                    refine ⟨84325912729493738315147221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112434550305991651086862961 84325912729493738315147221)
                    ·
                      refine ⟨1976388579597509491761263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84325912729493738315147221 1976388579597509491761263)
                      ·
                        rfl

theorem cell23_3849003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_3849003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849003 prefixEnd_3849003 := by exact prefixLift 3849003
  have htrace : WordTrace (prefixWord ++ tailWord_3849003) baseStart_3849003 baseEnd_3849003 := by
    simpa [prefixWord, tailWord_3849003, baseEnd_3849003] using wordTrace_append hprefix tailTrace_3849003
  have hstable : (prefixWord ++ tailWord_3849003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849003).length < 2 ^ (prefixWord ++ tailWord_3849003).sum := by decide
  have hdescent : baseEnd_3849003 < baseStart_3849003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849078 : List Nat := [5, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_3849078 : Nat := 118140960795 + 3849078 * 2 ^ 59
def prefixEnd_3849078 : Nat := 4983230072969 + 3 ^ 40 * 3849078 * 2
def baseEnd_3849078 : Nat := 219603010071844077591491

theorem tailTrace_3849078 : CollatzResearch.WordTrace tailWord_3849078 prefixEnd_3849078 219603010071844077591491 := by
  unfold tailWord_3849078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8774212996840953189474743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93591605299636834021063925 8774212996840953189474743)
  ·
    refine ⟨13161319495261429784212115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8774212996840953189474743 13161319495261429784212115)
    ·
      refine ⟨19741979242892144676318173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13161319495261429784212115 19741979242892144676318173)
      ·
        refine ⟨7403242216084554253619315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19741979242892144676318173 7403242216084554253619315)
        ·
          refine ⟨11104863324126831380428973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403242216084554253619315 11104863324126831380428973)
          ·
            refine ⟨4164323746547561767660865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11104863324126831380428973 4164323746547561767660865)
            ·
              refine ⟨3123242809910671325745649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4164323746547561767660865 3123242809910671325745649)
              ·
                refine ⟨2342432107433003494309237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123242809910671325745649 2342432107433003494309237)
                ·
                  refine ⟨219603010071844077591491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342432107433003494309237 219603010071844077591491)
                  ·
                    rfl

theorem cell23_3849078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_3849078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849078 prefixEnd_3849078 := by exact prefixLift 3849078
  have htrace : WordTrace (prefixWord ++ tailWord_3849078) baseStart_3849078 baseEnd_3849078 := by
    simpa [prefixWord, tailWord_3849078, baseEnd_3849078] using wordTrace_append hprefix tailTrace_3849078
  have hstable : (prefixWord ++ tailWord_3849078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849078).length < 2 ^ (prefixWord ++ tailWord_3849078).sum := by decide
  have hdescent : baseEnd_3849078 < baseStart_3849078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849114 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3849114 : Nat := 118140960795 + 3849114 * 2 ^ 59
def prefixEnd_3849114 : Nat := 4983230072969 + 3 ^ 40 * 3849114 * 2
def baseEnd_3849114 : Nat := 1976445575950158557473253

theorem tailTrace_3849114 : CollatzResearch.WordTrace tailWord_3849114 prefixEnd_3849114 1976445575950158557473253 := by
  unfold tailWord_3849114
  simp only [CollatzResearch.WordTrace]
  refine ⟨35097180244331207294976599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93592480651549886119937597 35097180244331207294976599)
  ·
    refine ⟨52645770366496810942464899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35097180244331207294976599 52645770366496810942464899)
    ·
      refine ⟨78968655549745216413697349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52645770366496810942464899 78968655549745216413697349)
      ·
        refine ⟨14806622915577228077568253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78968655549745216413697349 14806622915577228077568253)
        ·
          refine ⟨5552483593341460529088095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14806622915577228077568253 5552483593341460529088095)
          ·
            refine ⟨8328725390012190793632143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552483593341460529088095 8328725390012190793632143)
            ·
              refine ⟨12493088085018286190448215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8328725390012190793632143 12493088085018286190448215)
              ·
                refine ⟨18739632127527429285672323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12493088085018286190448215 18739632127527429285672323)
                ·
                  refine ⟨28109448191291143928508485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18739632127527429285672323 28109448191291143928508485)
                  ·
                    refine ⟨5270521535867089486595341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28109448191291143928508485 5270521535867089486595341)
                    ·
                      refine ⟨1976445575950158557473253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5270521535867089486595341 1976445575950158557473253)
                      ·
                        rfl

theorem cell23_3849114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3849114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849114 prefixEnd_3849114 := by exact prefixLift 3849114
  have htrace : WordTrace (prefixWord ++ tailWord_3849114) baseStart_3849114 baseEnd_3849114 := by
    simpa [prefixWord, tailWord_3849114, baseEnd_3849114] using wordTrace_append hprefix tailTrace_3849114
  have hstable : (prefixWord ++ tailWord_3849114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849114).length < 2 ^ (prefixWord ++ tailWord_3849114).sum := by decide
  have hdescent : baseEnd_3849114 < baseStart_3849114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849121 : List Nat := [1, 2, 3, 4, 1, 1, 1, 5, 1, 4]
def baseStart_3849121 : Nat := 118140960795 + 3849121 * 2 ^ 59
def prefixEnd_3849121 : Nat := 4983230072969 + 3 ^ 40 * 3849121 * 2
def baseEnd_3849121 : Nat := 658816390104913343361907

theorem tailTrace_3849121 : CollatzResearch.WordTrace tailWord_3849121 prefixEnd_3849121 658816390104913343361907 := by
  unfold tailWord_3849121
  simp only [CollatzResearch.WordTrace]
  refine ⟨140388976288299469375411217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93592650858866312916940811 140388976288299469375411217)
  ·
    refine ⟨105291732216224602031558413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140388976288299469375411217 105291732216224602031558413)
    ·
      refine ⟨39484399581084225761834405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105291732216224602031558413 39484399581084225761834405)
      ·
        refine ⟨7403324921453292330343951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39484399581084225761834405 7403324921453292330343951)
        ·
          refine ⟨11104987382179938495515927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403324921453292330343951 11104987382179938495515927)
          ·
            refine ⟨16657481073269907743273891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11104987382179938495515927 16657481073269907743273891)
            ·
              refine ⟨24986221609904861614910837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16657481073269907743273891 24986221609904861614910837)
              ·
                refine ⟨2342458275928580776397891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24986221609904861614910837 2342458275928580776397891)
                ·
                  refine ⟨3513687413892871164596837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342458275928580776397891 3513687413892871164596837)
                  ·
                    refine ⟨658816390104913343361907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3513687413892871164596837 658816390104913343361907)
                    ·
                      rfl

theorem cell23_3849121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_3849121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849121 prefixEnd_3849121 := by exact prefixLift 3849121
  have htrace : WordTrace (prefixWord ++ tailWord_3849121) baseStart_3849121 baseEnd_3849121 := by
    simpa [prefixWord, tailWord_3849121, baseEnd_3849121] using wordTrace_append hprefix tailTrace_3849121
  have hstable : (prefixWord ++ tailWord_3849121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849121).length < 2 ^ (prefixWord ++ tailWord_3849121).sum := by decide
  have hdescent : baseEnd_3849121 < baseStart_3849121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849144 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 3, 1, 3]
def baseStart_3849144 : Nat := 118140960795 + 3849144 * 2 ^ 59
def prefixEnd_3849144 : Nat := 4983230072969 + 3 ^ 40 * 3849144 * 2
def baseEnd_3849144 : Nat := 1976460980369793440098115

theorem tailTrace_3849144 : CollatzResearch.WordTrace tailWord_3849144 prefixEnd_3849144 1976460980369793440098115 := by
  unfold tailWord_3849144
  simp only [CollatzResearch.WordTrace]
  refine ⟨70194907583608072151749243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93593210111477429535665657 70194907583608072151749243)
  ·
    refine ⟨105292361375412108227623865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70194907583608072151749243 105292361375412108227623865)
    ·
      refine ⟨78969271031559081170717899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105292361375412108227623865 78969271031559081170717899)
      ·
        refine ⟨118453906547338621756076849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78969271031559081170717899 118453906547338621756076849)
        ·
          refine ⟨88840429910503966317057637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118453906547338621756076849 88840429910503966317057637)
          ·
            refine ⟨16657580608219493684448307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88840429910503966317057637 16657580608219493684448307)
            ·
              refine ⟨24986370912329240526672461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16657580608219493684448307 24986370912329240526672461)
              ·
                refine ⟨9369889092123465197502173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24986370912329240526672461 9369889092123465197502173)
                ·
                  refine ⟨3513708409546299449063315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9369889092123465197502173 3513708409546299449063315)
                  ·
                    refine ⟨5270562614319449173594973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3513708409546299449063315 5270562614319449173594973)
                    ·
                      refine ⟨1976460980369793440098115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5270562614319449173594973 1976460980369793440098115)
                      ·
                        rfl

theorem cell23_3849144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_3849144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849144 prefixEnd_3849144 := by exact prefixLift 3849144
  have htrace : WordTrace (prefixWord ++ tailWord_3849144) baseStart_3849144 baseEnd_3849144 := by
    simpa [prefixWord, tailWord_3849144, baseEnd_3849144] using wordTrace_append hprefix tailTrace_3849144
  have hstable : (prefixWord ++ tailWord_3849144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849144).length < 2 ^ (prefixWord ++ tailWord_3849144).sum := by decide
  have hdescent : baseEnd_3849144 < baseStart_3849144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849164 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_3849164 : Nat := 118140960795 + 3849164 * 2 ^ 59
def prefixEnd_3849164 : Nat := 4983230072969 + 3 ^ 40 * 3849164 * 2
def baseEnd_3849164 : Nat := 658823749994294453949341

theorem tailTrace_3849164 : CollatzResearch.WordTrace tailWord_3849164 prefixEnd_3849164 658823749994294453949341 := by
  unfold tailWord_3849164
  simp only [CollatzResearch.WordTrace]
  refine ⟨70195272313571843859613273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93593696418095791812817697 70195272313571843859613273)
  ·
    refine ⟨52646454235178882894709955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70195272313571843859613273 52646454235178882894709955)
    ·
      refine ⟨78969681352768324342064933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52646454235178882894709955 78969681352768324342064933)
      ·
        refine ⟨14806815253644060814137175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78969681352768324342064933 14806815253644060814137175)
        ·
          refine ⟨22210222880466091221205763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14806815253644060814137175 22210222880466091221205763)
          ·
            refine ⟨33315334320699136831808645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22210222880466091221205763 33315334320699136831808645)
            ·
              refine ⟨6246625185131088155964121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33315334320699136831808645 6246625185131088155964121)
              ·
                refine ⟨4684968888848316116973091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6246625185131088155964121 4684968888848316116973091)
                ·
                  refine ⟨7027453333272474175459637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684968888848316116973091 7027453333272474175459637)
                  ·
                    refine ⟨658823749994294453949341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7027453333272474175459637 658823749994294453949341)
                    ·
                      rfl

theorem cell23_3849164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_3849164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849164 prefixEnd_3849164 := by exact prefixLift 3849164
  have htrace : WordTrace (prefixWord ++ tailWord_3849164) baseStart_3849164 baseEnd_3849164 := by
    simpa [prefixWord, tailWord_3849164, baseEnd_3849164] using wordTrace_append hprefix tailTrace_3849164
  have hstable : (prefixWord ++ tailWord_3849164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849164).length < 2 ^ (prefixWord ++ tailWord_3849164).sum := by decide
  have hdescent : baseEnd_3849164 < baseStart_3849164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849178 : List Nat := [3, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3]
def baseStart_3849178 : Nat := 118140960795 + 3849178 * 2 ^ 59
def prefixEnd_3849178 : Nat := 4983230072969 + 3 ^ 40 * 3849178 * 2
def baseEnd_3849178 : Nat := 1976478438712046307072959

theorem tailTrace_3849178 : CollatzResearch.WordTrace tailWord_3849178 prefixEnd_3849178 1976478438712046307072959 := by
  unfold tailWord_3849178
  simp only [CollatzResearch.WordTrace]
  refine ⟨35097763812273242027559047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93594036832728645406824125 35097763812273242027559047)
  ·
    refine ⟨52646645718409863041338571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35097763812273242027559047 52646645718409863041338571)
    ·
      refine ⟨78969968577614794562007857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52646645718409863041338571 78969968577614794562007857)
      ·
        refine ⟨59227476433211095921505893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78969968577614794562007857 59227476433211095921505893)
        ·
          refine ⟨11105151831227080485282355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59227476433211095921505893 11105151831227080485282355)
          ·
            refine ⟨16657727746840620727923533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11105151831227080485282355 16657727746840620727923533)
            ·
              refine ⟨6246647905065232772971325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16657727746840620727923533 6246647905065232772971325)
              ·
                refine ⟨2342492964399462289864247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6246647905065232772971325 2342492964399462289864247)
                ·
                  refine ⟨3513739446599193434796371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342492964399462289864247 3513739446599193434796371)
                  ·
                    refine ⟨5270609169898790152194557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3513739446599193434796371 5270609169898790152194557)
                    ·
                      refine ⟨1976478438712046307072959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5270609169898790152194557 1976478438712046307072959)
                      ·
                        rfl

theorem cell23_3849178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_3849178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849178 prefixEnd_3849178 := by exact prefixLift 3849178
  have htrace : WordTrace (prefixWord ++ tailWord_3849178) baseStart_3849178 baseEnd_3849178 := by
    simpa [prefixWord, tailWord_3849178, baseEnd_3849178] using wordTrace_append hprefix tailTrace_3849178
  have hstable : (prefixWord ++ tailWord_3849178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849178).length < 2 ^ (prefixWord ++ tailWord_3849178).sum := by decide
  have hdescent : baseEnd_3849178 < baseStart_3849178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849194 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_3849194 : Nat := 118140960795 + 3849194 * 2 ^ 59
def prefixEnd_3849194 : Nat := 4983230072969 + 3 ^ 40 * 3849194 * 2
def baseEnd_3849194 : Nat := 658828884800839414824295

theorem tailTrace_3849194 : CollatzResearch.WordTrace tailWord_3849194 prefixEnd_3849194 658828884800839414824295 := by
  unfold tailWord_3849194
  simp only [CollatzResearch.WordTrace]
  refine ⟨35097909704258750710704659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93594425878023335228545757 35097909704258750710704659)
  ·
    refine ⟨52646864556388126066056989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35097909704258750710704659 52646864556388126066056989)
    ·
      refine ⟨19742574208645547274771371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52646864556388126066056989 19742574208645547274771371)
      ·
        refine ⟨29613861312968320912157057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19742574208645547274771371 29613861312968320912157057)
        ·
          refine ⟨22210395984726240684117793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29613861312968320912157057 22210395984726240684117793)
          ·
            refine ⟨16657796988544680513088345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22210395984726240684117793 16657796988544680513088345)
            ·
              refine ⟨12493347741408510384816259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16657796988544680513088345 12493347741408510384816259)
              ·
                refine ⟨18740021612112765577224389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12493347741408510384816259 18740021612112765577224389)
                ·
                  refine ⟨3513754052271143545729573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18740021612112765577224389 3513754052271143545729573)
                  ·
                    refine ⟨658828884800839414824295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3513754052271143545729573 658828884800839414824295)
                    ·
                      rfl

theorem cell23_3849194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_3849194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849194 prefixEnd_3849194 := by exact prefixLift 3849194
  have htrace : WordTrace (prefixWord ++ tailWord_3849194) baseStart_3849194 baseEnd_3849194 := by
    simpa [prefixWord, tailWord_3849194, baseEnd_3849194] using wordTrace_append hprefix tailTrace_3849194
  have hstable : (prefixWord ++ tailWord_3849194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849194).length < 2 ^ (prefixWord ++ tailWord_3849194).sum := by decide
  have hdescent : baseEnd_3849194 < baseStart_3849194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849218 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3849218 : Nat := 118140960795 + 3849218 * 2 ^ 59
def prefixEnd_3849218 : Nat := 4983230072969 + 3 ^ 40 * 3849218 * 2
def baseEnd_3849218 : Nat := 1976498977938226150572775

theorem tailTrace_3849218 : CollatzResearch.WordTrace tailWord_3849218 prefixEnd_3849218 1976498977938226150572775 := by
  unfold tailWord_3849218
  simp only [CollatzResearch.WordTrace]
  refine ⟨35098128542237013735423077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93595009445965369961128205 35098128542237013735423077)
  ·
    refine ⟨6580899101669440075391827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35098128542237013735423077 6580899101669440075391827)
    ·
      refine ⟨9871348652504160113087741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6580899101669440075391827 9871348652504160113087741)
      ·
        refine ⟨3701755744689060042407903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9871348652504160113087741 3701755744689060042407903)
        ·
          refine ⟨5552633617033590063611855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701755744689060042407903 5552633617033590063611855)
          ·
            refine ⟨8328950425550385095417783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552633617033590063611855 8328950425550385095417783)
            ·
              refine ⟨12493425638325577643126675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8328950425550385095417783 12493425638325577643126675)
              ·
                refine ⟨18740138457488366464690013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12493425638325577643126675 18740138457488366464690013)
                ·
                  refine ⟨7027551921558137424258755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18740138457488366464690013 7027551921558137424258755)
                  ·
                    refine ⟨10541327882337206136388133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7027551921558137424258755 10541327882337206136388133)
                    ·
                      refine ⟨1976498977938226150572775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10541327882337206136388133 1976498977938226150572775)
                      ·
                        rfl

theorem cell23_3849218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3849218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849218 prefixEnd_3849218 := by exact prefixLift 3849218
  have htrace : WordTrace (prefixWord ++ tailWord_3849218) baseStart_3849218 baseEnd_3849218 := by
    simpa [prefixWord, tailWord_3849218, baseEnd_3849218] using wordTrace_append hprefix tailTrace_3849218
  have hstable : (prefixWord ++ tailWord_3849218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849218).length < 2 ^ (prefixWord ++ tailWord_3849218).sum := by decide
  have hdescent : baseEnd_3849218 < baseStart_3849218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849251 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 3]
def baseStart_3849251 : Nat := 118140960795 + 3849251 * 2 ^ 59
def prefixEnd_3849251 : Nat := 4983230072969 + 3 ^ 40 * 3849251 * 2
def baseEnd_3849251 : Nat := 1976515922799824521460123

theorem tailTrace_3849251 : CollatzResearch.WordTrace tailWord_3849251 prefixEnd_3849251 1976515922799824521460123 := by
  unfold tailWord_3849251
  simp only [CollatzResearch.WordTrace]
  refine ⟨140393717777828501577643607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93595811851885667718429071 140393717777828501577643607)
  ·
    refine ⟨210590576666742752366465411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140393717777828501577643607 210590576666742752366465411)
    ·
      refine ⟨315885865000114128549698117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210590576666742752366465411 315885865000114128549698117)
      ·
        refine ⟨59228599687521399103068397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315885865000114128549698117 59228599687521399103068397)
        ·
          refine ⟨22210724882820524663650649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59228599687521399103068397 22210724882820524663650649)
          ·
            refine ⟨16658043662115393497737987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22210724882820524663650649 16658043662115393497737987)
            ·
              refine ⟨24987065493173090246606981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16658043662115393497737987 24987065493173090246606981)
              ·
                refine ⟨4685074779969954421238809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24987065493173090246606981 4685074779969954421238809)
                ·
                  refine ⟨3513806084977465815929107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4685074779969954421238809 3513806084977465815929107)
                  ·
                    refine ⟨5270709127466198723893661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3513806084977465815929107 5270709127466198723893661)
                    ·
                      refine ⟨1976515922799824521460123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5270709127466198723893661 1976515922799824521460123)
                      ·
                        rfl

theorem cell23_3849251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_3849251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849251 prefixEnd_3849251 := by exact prefixLift 3849251
  have htrace : WordTrace (prefixWord ++ tailWord_3849251) baseStart_3849251 baseEnd_3849251 := by
    simpa [prefixWord, tailWord_3849251, baseEnd_3849251] using wordTrace_append hprefix tailTrace_3849251
  have hstable : (prefixWord ++ tailWord_3849251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849251).length < 2 ^ (prefixWord ++ tailWord_3849251).sum := by decide
  have hdescent : baseEnd_3849251 < baseStart_3849251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849252 : List Nat := [2, 3, 1, 4, 1, 1, 4, 2, 1, 2, 2]
def baseStart_3849252 : Nat := 118140960795 + 3849252 * 2 ^ 59
def prefixEnd_3849252 : Nat := 4983230072969 + 3 ^ 40 * 3849252 * 2
def baseEnd_3849252 : Nat := 1976516436280479017547619

theorem tailTrace_3849252 : CollatzResearch.WordTrace tailWord_3849252 prefixEnd_3849252 1976516436280479017547619 := by
  unfold tailWord_3849252
  simp only [CollatzResearch.WordTrace]
  refine ⟨70196877125412439374215005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93595836167216585832286673 70196877125412439374215005)
  ·
    refine ⟨26323828922029664765330627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70196877125412439374215005 26323828922029664765330627)
    ·
      refine ⟨39485743383044497147995941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26323828922029664765330627 39485743383044497147995941)
      ·
        refine ⟨7403576884320843215249239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39485743383044497147995941 7403576884320843215249239)
        ·
          refine ⟨11105365326481264822873859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403576884320843215249239 11105365326481264822873859)
          ·
            refine ⟨16658047989721897234310789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11105365326481264822873859 16658047989721897234310789)
            ·
              refine ⟨3123383998072855731433273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16658047989721897234310789 3123383998072855731433273)
              ·
                refine ⟨2342537998554641798574955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123383998072855731433273 2342537998554641798574955)
                ·
                  refine ⟨3513806997831962697862433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342537998554641798574955 3513806997831962697862433)
                  ·
                    refine ⟨2635355248373972023396825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3513806997831962697862433 2635355248373972023396825)
                    ·
                      refine ⟨1976516436280479017547619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2635355248373972023396825 1976516436280479017547619)
                      ·
                        rfl

theorem cell23_3849252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_3849252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849252 prefixEnd_3849252 := by exact prefixLift 3849252
  have htrace : WordTrace (prefixWord ++ tailWord_3849252) baseStart_3849252 baseEnd_3849252 := by
    simpa [prefixWord, tailWord_3849252, baseEnd_3849252] using wordTrace_append hprefix tailTrace_3849252
  have hstable : (prefixWord ++ tailWord_3849252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849252).length < 2 ^ (prefixWord ++ tailWord_3849252).sum := by decide
  have hdescent : baseEnd_3849252 < baseStart_3849252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849268 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3849268 : Nat := 118140960795 + 3849268 * 2 ^ 59
def prefixEnd_3849268 : Nat := 4983230072969 + 3 ^ 40 * 3849268 * 2
def baseEnd_3849268 : Nat := 1976524651970950954947545

theorem tailTrace_3849268 : CollatzResearch.WordTrace tailWord_3849268 prefixEnd_3849268 1976524651970950954947545 := by
  unfold tailWord_3849268
  simp only [CollatzResearch.WordTrace]
  refine ⟨70197168909383456740506229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93596225212511275654008305 70197168909383456740506229)
  ·
    refine ⟨6580984585254699069422459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70197168909383456740506229 6580984585254699069422459)
    ·
      refine ⟨9871476877882048604133689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6580984585254699069422459 9871476877882048604133689)
      ·
        refine ⟨7403607658411536453100267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9871476877882048604133689 7403607658411536453100267)
        ·
          refine ⟨11105411487617304679650401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403607658411536453100267 11105411487617304679650401)
          ·
            refine ⟨8329058615712978509737801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11105411487617304679650401 8329058615712978509737801)
            ·
              refine ⟨6246793961784733882303351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8329058615712978509737801 6246793961784733882303351)
              ·
                refine ⟨9370190942677100823455027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246793961784733882303351 9370190942677100823455027)
                ·
                  refine ⟨14055286414015651235182541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9370190942677100823455027 14055286414015651235182541)
                  ·
                    refine ⟨5270732405255869213193453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14055286414015651235182541 5270732405255869213193453)
                    ·
                      refine ⟨1976524651970950954947545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5270732405255869213193453 1976524651970950954947545)
                      ·
                        rfl

theorem cell23_3849268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3849268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849268 prefixEnd_3849268 := by exact prefixLift 3849268
  have htrace : WordTrace (prefixWord ++ tailWord_3849268) baseStart_3849268 baseEnd_3849268 := by
    simpa [prefixWord, tailWord_3849268, baseEnd_3849268] using wordTrace_append hprefix tailTrace_3849268
  have hstable : (prefixWord ++ tailWord_3849268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849268).length < 2 ^ (prefixWord ++ tailWord_3849268).sum := by decide
  have hdescent : baseEnd_3849268 < baseStart_3849268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849278 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_3849278 : Nat := 118140960795 + 3849278 * 2 ^ 59
def prefixEnd_3849278 : Nat := 4983230072969 + 3 ^ 40 * 3849278 * 2
def baseEnd_3849278 : Nat := 1976529786777495915822499

theorem tailTrace_3849278 : CollatzResearch.WordTrace tailWord_3849278 prefixEnd_3849278 1976529786777495915822499 := by
  unfold tailWord_3849278
  simp only [CollatzResearch.WordTrace]
  refine ⟨17549337818591335648609561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93596468365820456792584325 17549337818591335648609561)
  ·
    refine ⟨13162003363943501736457171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17549337818591335648609561 13162003363943501736457171)
    ·
      refine ⟨19743005045915252604685757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13162003363943501736457171 19743005045915252604685757)
      ·
        refine ⟨7403626892218219726757159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19743005045915252604685757 7403626892218219726757159)
        ·
          refine ⟨11105440338327329590135739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403626892218219726757159 11105440338327329590135739)
          ·
            refine ⟨16658160507490994385203609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11105440338327329590135739 16658160507490994385203609)
            ·
              refine ⟨12493620380618245788902707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16658160507490994385203609 12493620380618245788902707)
              ·
                refine ⟨18740430570927368683354061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12493620380618245788902707 18740430570927368683354061)
                ·
                  refine ⟨7027661464097763256257773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18740430570927368683354061 7027661464097763256257773)
                  ·
                    refine ⟨2635373049036661221096665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7027661464097763256257773 2635373049036661221096665)
                    ·
                      refine ⟨1976529786777495915822499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2635373049036661221096665 1976529786777495915822499)
                      ·
                        rfl

theorem cell23_3849278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_3849278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849278 prefixEnd_3849278 := by exact prefixLift 3849278
  have htrace : WordTrace (prefixWord ++ tailWord_3849278) baseStart_3849278 baseEnd_3849278 := by
    simpa [prefixWord, tailWord_3849278, baseEnd_3849278] using wordTrace_append hprefix tailTrace_3849278
  have hstable : (prefixWord ++ tailWord_3849278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849278).length < 2 ^ (prefixWord ++ tailWord_3849278).sum := by decide
  have hdescent : baseEnd_3849278 < baseStart_3849278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849308 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_3849308 : Nat := 118140960795 + 3849308 * 2 ^ 59
def prefixEnd_3849308 : Nat := 4983230072969 + 3 ^ 40 * 3849308 * 2
def baseEnd_3849308 : Nat := 1976545191197130798447361

theorem tailTrace_3849308 : CollatzResearch.WordTrace tailWord_3849308 prefixEnd_3849308 1976545191197130798447361 := by
  unfold tailWord_3849308
  simp only [CollatzResearch.WordTrace]
  refine ⟨70197898369311000156234289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93597197825748000208312385 70197898369311000156234289)
  ·
    refine ⟨52648423776983250117175717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70197898369311000156234289 52648423776983250117175717)
    ·
      refine ⟨9871579458184359396970447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52648423776983250117175717 9871579458184359396970447)
      ·
        refine ⟨14807369187276539095455671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9871579458184359396970447 14807369187276539095455671)
        ·
          refine ⟨22211053780914808643183507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14807369187276539095455671 22211053780914808643183507)
          ·
            refine ⟨33316580671372212964775261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22211053780914808643183507 33316580671372212964775261)
            ·
              refine ⟨12493717751764579861790723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33316580671372212964775261 12493717751764579861790723)
              ·
                refine ⟨18740576627646869792686085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12493717751764579861790723 18740576627646869792686085)
                ·
                  refine ⟨3513858117683788086128641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18740576627646869792686085 3513858117683788086128641)
                  ·
                    refine ⟨2635393588262841064596481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3513858117683788086128641 2635393588262841064596481)
                    ·
                      refine ⟨1976545191197130798447361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2635393588262841064596481 1976545191197130798447361)
                      ·
                        rfl

theorem cell23_3849308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_3849308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849308 prefixEnd_3849308 := by exact prefixLift 3849308
  have htrace : WordTrace (prefixWord ++ tailWord_3849308) baseStart_3849308 baseEnd_3849308 := by
    simpa [prefixWord, tailWord_3849308, baseEnd_3849308] using wordTrace_append hprefix tailTrace_3849308
  have hstable : (prefixWord ++ tailWord_3849308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849308).length < 2 ^ (prefixWord ++ tailWord_3849308).sum := by decide
  have hdescent : baseEnd_3849308 < baseStart_3849308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849324 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_3849324 : Nat := 118140960795 + 3849324 * 2 ^ 59
def prefixEnd_3849324 : Nat := 4983230072969 + 3 ^ 40 * 3849324 * 2
def baseEnd_3849324 : Nat := 1976553406887602735847287

theorem tailTrace_3849324 : CollatzResearch.WordTrace tailWord_3849324 prefixEnd_3849324 1976553406887602735847287 := by
  unfold tailWord_3849324
  simp only [CollatzResearch.WordTrace]
  refine ⟨70198190153282017522525513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93597586871042690030034017 70198190153282017522525513)
  ·
    refine ⟨52648642614961513141894135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70198190153282017522525513 52648642614961513141894135)
    ·
      refine ⟨78972963922442269712841203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52648642614961513141894135 78972963922442269712841203)
      ·
        refine ⟨118459445883663404569261805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78972963922442269712841203 118459445883663404569261805)
        ·
          refine ⟨44422292206373776713473177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118459445883663404569261805 44422292206373776713473177)
          ·
            refine ⟨33316719154780332535104883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44422292206373776713473177 33316719154780332535104883)
            ·
              refine ⟨49975078732170498802657325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33316719154780332535104883 49975078732170498802657325)
              ·
                refine ⟨18740654524563937050996497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49975078732170498802657325 18740654524563937050996497)
                ·
                  refine ⟨14055490893422952788247373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18740654524563937050996497 14055490893422952788247373)
                  ·
                    refine ⟨5270809085033607295592765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14055490893422952788247373 5270809085033607295592765)
                    ·
                      refine ⟨1976553406887602735847287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5270809085033607295592765 1976553406887602735847287)
                      ·
                        rfl

theorem cell23_3849324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_3849324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849324 prefixEnd_3849324 := by exact prefixLift 3849324
  have htrace : WordTrace (prefixWord ++ tailWord_3849324) baseStart_3849324 baseEnd_3849324 := by
    simpa [prefixWord, tailWord_3849324, baseEnd_3849324] using wordTrace_append hprefix tailTrace_3849324
  have hstable : (prefixWord ++ tailWord_3849324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849324).length < 2 ^ (prefixWord ++ tailWord_3849324).sum := by decide
  have hdescent : baseEnd_3849324 < baseStart_3849324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849327 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 3, 7]
def baseStart_3849327 : Nat := 118140960795 + 3849327 * 2 ^ 59
def prefixEnd_3849327 : Nat := 4983230072969 + 3 ^ 40 * 3849327 * 2
def baseEnd_3849327 : Nat := 658851649109855408036591

theorem tailTrace_3849327 : CollatzResearch.WordTrace tailWord_3849327 prefixEnd_3849327 658851649109855408036591 := by
  unfold tailWord_3849327
  simp only [CollatzResearch.WordTrace]
  refine ⟨140396489725553166557410235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93597659817035444371606823 140396489725553166557410235)
  ·
    refine ⟨210594734588329749836115353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140396489725553166557410235 210594734588329749836115353)
    ·
      refine ⟨157946050941247312377086515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210594734588329749836115353 157946050941247312377086515)
      ·
        refine ⟨236919076411870968565629773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157946050941247312377086515 236919076411870968565629773)
        ·
          refine ⟨88844653654451613212111165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236919076411870968565629773 88844653654451613212111165)
          ·
            refine ⟨33316745120419354954541687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88844653654451613212111165 33316745120419354954541687)
            ·
              refine ⟨49975117680629032431812531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33316745120419354954541687 49975117680629032431812531)
              ·
                refine ⟨74962676520943548647718797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49975117680629032431812531 74962676520943548647718797)
                ·
                  refine ⟨28111003695353830742894549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74962676520943548647718797 28111003695353830742894549)
                  ·
                    refine ⟨658851649109855408036591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28111003695353830742894549 658851649109855408036591)
                    ·
                      rfl

theorem cell23_3849327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_3849327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849327 prefixEnd_3849327 := by exact prefixLift 3849327
  have htrace : WordTrace (prefixWord ++ tailWord_3849327) baseStart_3849327 baseEnd_3849327 := by
    simpa [prefixWord, tailWord_3849327, baseEnd_3849327] using wordTrace_append hprefix tailTrace_3849327
  have hstable : (prefixWord ++ tailWord_3849327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849327).length < 2 ^ (prefixWord ++ tailWord_3849327).sum := by decide
  have hdescent : baseEnd_3849327 < baseStart_3849327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849348 : List Nat := [2, 3, 2, 1, 2, 4, 1, 3, 5]
def baseStart_3849348 : Nat := 118140960795 + 3849348 * 2 ^ 59
def prefixEnd_3849348 : Nat := 4983230072969 + 3 ^ 40 * 3849348 * 2
def baseEnd_3849348 : Nat := 219618414491478960216353

theorem tailTrace_3849348 : CollatzResearch.WordTrace tailWord_3849348 prefixEnd_3849348 219618414491478960216353 := by
  unfold tailWord_3849348
  simp only [CollatzResearch.WordTrace]
  refine ⟨70198627829238543571962349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93598170438984724762616465 70198627829238543571962349)
  ·
    refine ⟨26324485435964453839485881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70198627829238543571962349 26324485435964453839485881)
    ·
      refine ⟨19743364076973340379614411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26324485435964453839485881 19743364076973340379614411)
      ·
        refine ⟨29615046115460010569421617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19743364076973340379614411 29615046115460010569421617)
        ·
          refine ⟨22211284586595007927066213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29615046115460010569421617 22211284586595007927066213)
          ·
            refine ⟨4164615859986563986324915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22211284586595007927066213 4164615859986563986324915)
            ·
              refine ⟨6246923789979845979487373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164615859986563986324915 6246923789979845979487373)
              ·
                refine ⟨2342596421242442242307765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6246923789979845979487373 2342596421242442242307765)
                ·
                  refine ⟨219618414491478960216353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342596421242442242307765 219618414491478960216353)
                  ·
                    rfl

theorem cell23_3849348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_3849348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849348 prefixEnd_3849348 := by exact prefixLift 3849348
  have htrace : WordTrace (prefixWord ++ tailWord_3849348) baseStart_3849348 baseEnd_3849348 := by
    simpa [prefixWord, tailWord_3849348, baseEnd_3849348] using wordTrace_append hprefix tailTrace_3849348
  have hstable : (prefixWord ++ tailWord_3849348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849348).length < 2 ^ (prefixWord ++ tailWord_3849348).sum := by decide
  have hdescent : baseEnd_3849348 < baseStart_3849348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849354 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3849354 : Nat := 118140960795 + 3849354 * 2 ^ 59
def prefixEnd_3849354 : Nat := 4983230072969 + 3 ^ 40 * 3849354 * 2
def baseEnd_3849354 : Nat := 1976568811307237618472149

theorem tailTrace_3849354 : CollatzResearch.WordTrace tailWord_3849354 prefixEnd_3849354 1976568811307237618472149 := by
  unfold tailWord_3849354
  simp only [CollatzResearch.WordTrace]
  refine ⟨35099368624113837542160779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93598316330970233445762077 35099368624113837542160779)
  ·
    refine ⟨52649052936170756313241169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35099368624113837542160779 52649052936170756313241169)
    ·
      refine ⟨39486789702128067234930877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52649052936170756313241169 39486789702128067234930877)
      ·
        refine ⟨14807546138298025213099079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39486789702128067234930877 14807546138298025213099079)
        ·
          refine ⟨22211319207447037819648619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14807546138298025213099079 22211319207447037819648619)
          ·
            refine ⟨33316978811170556729472929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22211319207447037819648619 33316978811170556729472929)
            ·
              refine ⟨24987734108377917547104697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33316978811170556729472929 24987734108377917547104697)
              ·
                refine ⟨18740800581283438160328523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24987734108377917547104697 18740800581283438160328523)
                ·
                  refine ⟨28111200871925157240492785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18740800581283438160328523 28111200871925157240492785)
                  ·
                    refine ⟨21083400653943867930369589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28111200871925157240492785 21083400653943867930369589)
                    ·
                      refine ⟨1976568811307237618472149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21083400653943867930369589 1976568811307237618472149)
                      ·
                        rfl

theorem cell23_3849354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3849354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849354 prefixEnd_3849354 := by exact prefixLift 3849354
  have htrace : WordTrace (prefixWord ++ tailWord_3849354) baseStart_3849354 baseEnd_3849354 := by
    simpa [prefixWord, tailWord_3849354, baseEnd_3849354] using wordTrace_append hprefix tailTrace_3849354
  have hstable : (prefixWord ++ tailWord_3849354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849354).length < 2 ^ (prefixWord ++ tailWord_3849354).sum := by decide
  have hdescent : baseEnd_3849354 < baseStart_3849354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849401 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 3]
def baseStart_3849401 : Nat := 118140960795 + 3849401 * 2 ^ 59
def prefixEnd_3849401 : Nat := 4983230072969 + 3 ^ 40 * 3849401 * 2
def baseEnd_3849401 : Nat := 1976592944897998934584433

theorem tailTrace_3849401 : CollatzResearch.WordTrace tailWord_3849401 prefixEnd_3849401 1976592944897998934584433 := by
  unfold tailWord_3849401
  simp only [CollatzResearch.WordTrace]
  refine ⟨140399188727285077195604057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93599459151523384797069371 140399188727285077195604057)
  ·
    refine ⟨105299391545463807896703043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140399188727285077195604057 105299391545463807896703043)
    ·
      refine ⟨157949087318195711845054565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105299391545463807896703043 157949087318195711845054565)
      ·
        refine ⟨29615453872161695970947731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157949087318195711845054565 29615453872161695970947731)
        ·
          refine ⟨44423180808242543956421597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29615453872161695970947731 44423180808242543956421597)
          ·
            refine ⟨16658692803090953983658099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44423180808242543956421597 16658692803090953983658099)
            ·
              refine ⟨24988039204636430975487149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16658692803090953983658099 24988039204636430975487149)
              ·
                refine ⟨9370514701738661615807681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24988039204636430975487149 9370514701738661615807681)
                ·
                  refine ⟨7027886026303996211855761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9370514701738661615807681 7027886026303996211855761)
                  ·
                    refine ⟨5270914519727997158891821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7027886026303996211855761 5270914519727997158891821)
                    ·
                      refine ⟨1976592944897998934584433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5270914519727997158891821 1976592944897998934584433)
                      ·
                        rfl

theorem cell23_3849401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_3849401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849401 prefixEnd_3849401 := by exact prefixLift 3849401
  have htrace : WordTrace (prefixWord ++ tailWord_3849401) baseStart_3849401 baseEnd_3849401 := by
    simpa [prefixWord, tailWord_3849401, baseEnd_3849401] using wordTrace_append hprefix tailTrace_3849401
  have hstable : (prefixWord ++ tailWord_3849401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849401).length < 2 ^ (prefixWord ++ tailWord_3849401).sum := by decide
  have hdescent : baseEnd_3849401 < baseStart_3849401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3849448 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3849448 : Nat := 118140960795 + 3849448 * 2 ^ 59
def prefixEnd_3849448 : Nat := 4983230072969 + 3 ^ 40 * 3849448 * 2
def baseEnd_3849448 : Nat := 1976617078488760250696717

theorem tailTrace_3849448 : CollatzResearch.WordTrace tailWord_3849448 prefixEnd_3849448 1976617078488760250696717 := by
  unfold tailWord_3849448
  simp only [CollatzResearch.WordTrace]
  refine ⟨70200451479057402111282499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93600601972076536148376665 70200451479057402111282499)
  ·
    refine ⟨105300677218586103166923749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70200451479057402111282499 105300677218586103166923749)
    ·
      refine ⟨19743876978484894343798203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105300677218586103166923749 19743876978484894343798203)
      ·
        refine ⟨29615815467727341515697305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19743876978484894343798203 29615815467727341515697305)
        ·
          refine ⟨22211861600795506136772979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29615815467727341515697305 22211861600795506136772979)
          ·
            refine ⟨33317792401193259205159469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22211861600795506136772979 33317792401193259205159469)
            ·
              refine ⟨12494172150447472201934801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33317792401193259205159469 12494172150447472201934801)
              ·
                refine ⟨9370629112835604151451101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12494172150447472201934801 9370629112835604151451101)
                ·
                  refine ⟨3513985917313351556794163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9370629112835604151451101 3513985917313351556794163)
                  ·
                    refine ⟨5270978875970027335191245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3513985917313351556794163 5270978875970027335191245)
                    ·
                      refine ⟨1976617078488760250696717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5270978875970027335191245 1976617078488760250696717)
                      ·
                        rfl

theorem cell23_3849448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3849448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3849448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3849448 prefixEnd_3849448 := by exact prefixLift 3849448
  have htrace : WordTrace (prefixWord ++ tailWord_3849448) baseStart_3849448 baseEnd_3849448 := by
    simpa [prefixWord, tailWord_3849448, baseEnd_3849448] using wordTrace_append hprefix tailTrace_3849448
  have hstable : (prefixWord ++ tailWord_3849448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3849448).length < 2 ^ (prefixWord ++ tailWord_3849448).sum := by decide
  have hdescent : baseEnd_3849448 < baseStart_3849448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3849448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
